using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ComplexityAnalyzer;

public sealed class ComplexityAnalyzerService
{
    private static readonly HashSet<string> LinearOperations =
    [
        "Where", "Select", "SelectMany", "Any", "All", "Count", "LongCount",
        "First", "FirstOrDefault", "Single", "SingleOrDefault", "Last", "LastOrDefault",
        "Contains", "IndexOf", "Sum", "Min", "Max", "Average", "Aggregate",
        "ToList", "ToArray", "ToDictionary", "GroupBy", "Distinct", "Union", "Intersect", "Except",
        "Concat", "Zip", "Append", "Prepend", "Reverse", "TakeWhile", "SkipWhile", "SequenceEqual"
    ];

    public AnalysisResult Analyze(string source)
    {
        var warnings = new HashSet<string>(StringComparer.Ordinal);
        var assumptions = new HashSet<string>(StringComparer.Ordinal)
        {
            "Complexities describe worst-case growth as input size n increases; they are static estimates, not execution measurements.",
            "Recognized collection traversals and input-derived loop bounds are modeled against n, with constant-time operations assumed inside loops."
        };
        var syntaxTree = CSharpSyntaxTree.ParseText(source ?? string.Empty);
        var root = syntaxTree.GetRoot();
        var syntaxErrors = syntaxTree.GetDiagnostics()
            .Where(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
            .Select(diagnostic => $"Line {diagnostic.Location.GetLineSpan().StartLinePosition.Line + 1}: {diagnostic.GetMessage()}")
            .ToArray();

        if (string.IsNullOrWhiteSpace(source))
        {
            warnings.Add("Enter C# code to analyze.");
            return new AnalysisResult("—", "—", "No code was provided.", assumptions.ToArray(), warnings.ToArray(), 0, syntaxErrors);
        }

        if (syntaxErrors.Length > 0)
            warnings.Add("The input has syntax errors; results may be incomplete.");

        if (syntaxErrors.Length == 0 && TryRecognizeDijkstra(root))
        {
            assumptions.Add("Recognized Dijkstra estimates assume an adjacency-list graph and a binary priority queue that may hold duplicate entries.");
            assumptions.Add("The input graph is excluded from auxiliary space; distances and lazy priority-queue entries require O(V + E) space.");
            warnings.Add("The Dijkstra pattern is inferred syntactically; nonnegative edge weights and algorithm correctness are not verified.");
            return new AnalysisResult(
                "O((V + E) log E)",
                "O(V + E)",
                "A Dijkstra-style adjacency-list traversal with a priority queue and stale-entry guard was recognized.",
                assumptions.ToArray(),
                warnings.ToArray(),
                75,
                syntaxErrors);
        }

        if (syntaxErrors.Length == 0 && TryRecognizeHeapSort(root, out var heapSortSpace))
        {
            assumptions.Add("Recognized heap sort assumes an in-place binary heap over the input array; recursive sift-down, if present, adds logarithmic stack space.");
            warnings.Add("Heap-sort complexity is inferred from method structure; ordering and heap-property correctness are not verified.");
            return new AnalysisResult(
                "O(n log n)",
                heapSortSpace,
                "An in-place heap sort with heap construction and sift-down operations was recognized.",
                assumptions.ToArray(),
                warnings.ToArray(),
                75,
                syntaxErrors);
        }

        if (syntaxErrors.Length == 0 && TryRecognizeTopologicalSort(root))
        {
            assumptions.Add("Recognized Kahn-style topological sorting assumes an adjacency-list graph; the input graph is excluded from auxiliary space.");
            warnings.Add("Topological-sort complexity is inferred syntactically; graph validity and cycle handling are not verified.");
            return new AnalysisResult(
                "O(V + E)",
                "O(V)",
                "A queue-based topological traversal with indegree tracking was recognized.",
                assumptions.ToArray(),
                warnings.ToArray(),
                75,
                syntaxErrors);
        }

        if (syntaxErrors.Length == 0 && TryRecognizeAdditionalAlgorithm(root, out var recognizedAlgorithm))
        {
            assumptions.Add(recognizedAlgorithm.Assumption);
            warnings.Add(recognizedAlgorithm.Warning);
            return new AnalysisResult(
                recognizedAlgorithm.Time,
                recognizedAlgorithm.Space,
                recognizedAlgorithm.Explanation,
                assumptions.ToArray(),
                warnings.ToArray(),
                75,
                syntaxErrors);
        }

        var declaredMethods = root.DescendantNodes().OfType<MethodDeclarationSyntax>()
            .Select(method => method.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>().ToArray();
        if (methods.Length > 1)
            warnings.Add("Methods are estimated independently; the displayed complexity is the highest per-method estimate and does not compose the call graph.");
        var time = Complexity.Constant;
        var space = Complexity.Constant;
        var hasMethod = false;

        foreach (var method in methods)
        {
            if (method.Body is null && method.ExpressionBody is null)
                continue;

            hasMethod = true;
            var body = (SyntaxNode?)method.Body ?? method.ExpressionBody!.Expression;
            var hasUnanalyzedHelperCalls = HasUnanalyzedHelperCalls(body, method.Identifier.ValueText, declaredMethods);
            if (hasUnanalyzedHelperCalls)
                warnings.Add($"Method '{method.Identifier.ValueText}' calls another method in the input; call costs are not composed, so its time and auxiliary-space estimates are reported as unknown.");

            var methodTime = hasUnanalyzedHelperCalls ? Complexity.UnknownComplexity : AnalyzeNode(body, warnings, declaredMethods);
            var recursiveCalls = body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                .Count(invocation => GetInvokedName(invocation) == method.Identifier.ValueText);

            if (recursiveCalls > 0)
            {
                var localWork = hasUnanalyzedHelperCalls ? Complexity.UnknownComplexity : AnalyzeNode(body, warnings, declaredMethods);
                var recursiveCallsPerPath = GetRecursiveCallsPerPath(body, method.Identifier.ValueText);
                var recursiveCallInLoop = HasRecursiveCallInLoop(body, method.Identifier.ValueText, out var unknownLoopBound);
                methodTime = EstimateRecursion(method, recursiveCallsPerPath, recursiveCallInLoop, unknownLoopBound, localWork, warnings, assumptions);
                var recursiveStack = HasHalvingReduction(method) ? Complexity.Logarithmic :
                    HasLinearReduction(method) ? Complexity.Linear : Complexity.UnknownComplexity;
                space = Complexity.Max(space, recursiveStack);
            }

            time = Complexity.Max(time, methodTime);
            space = Complexity.Max(space, hasUnanalyzedHelperCalls ? Complexity.UnknownComplexity : AnalyzeSpace(body, warnings));
        }

        if (!hasMethod)
        {
            var globalStatements = root.DescendantNodes().OfType<GlobalStatementSyntax>().ToArray();
            if (globalStatements.Length > 0)
            {
                time = AnalyzeSequence(globalStatements.Select(statement => statement.Statement), warnings, declaredMethods);
                space = AnalyzeSpace(root, warnings);
            }
            else
            {
                warnings.Add("No method or top-level executable statements were found.");
            }
        }

        if (root.DescendantNodes().OfType<LambdaExpressionSyntax>().Any())
            warnings.Add("Lambda bodies and delegate invocation counts may depend on runtime behavior and are only partially represented.");

        var confidence = Math.Clamp(90 - warnings.Count * 8 - syntaxErrors.Length * 10, 15, 95);
        var explanation = "The estimate is based on recognized syntax constructs. Verify loop bounds, called methods, and runtime-dependent behavior against the actual input.";
        return new AnalysisResult(
            time.ToBigO(),
            space.ToBigO(),
            explanation,
            assumptions.ToArray(),
            warnings.ToArray(),
            confidence,
            syntaxErrors);
    }

    private static Complexity AnalyzeSequence(IEnumerable<StatementSyntax> statements, HashSet<string> warnings, HashSet<string> declaredMethods)
    {
        var result = Complexity.Constant;
        foreach (var statement in statements)
            result = Complexity.Max(result, AnalyzeNode(statement, warnings, declaredMethods));
        return result;
    }

    private static Complexity AnalyzeNode(SyntaxNode node, HashSet<string> warnings, HashSet<string> declaredMethods)
    {
        switch (node)
        {
            case BlockSyntax block:
                return AnalyzeSequence(block.Statements, warnings, declaredMethods);
            case ForStatementSyntax forStatement:
                if (IsCountingSortExpansion(forStatement))
                    return Complexity.Linear;
                return AnalyzeLoop(forStatement, forStatement.Statement, warnings, declaredMethods);
            case ForEachStatementSyntax forEach:
                return Complexity.Linear.Multiply(AnalyzeNode(forEach.Statement, warnings, declaredMethods));
            case ForEachVariableStatementSyntax forEachVariable:
                return Complexity.Linear.Multiply(AnalyzeNode(forEachVariable.Statement, warnings, declaredMethods));
            case WhileStatementSyntax whileStatement:
                return AnalyzeLoop(whileStatement, whileStatement.Statement, warnings, declaredMethods);
            case DoStatementSyntax doStatement:
                return AnalyzeLoop(doStatement, doStatement.Statement, warnings, declaredMethods);
            case IfStatementSyntax ifStatement:
                if (ifStatement.Condition.IsKind(SyntaxKind.TrueLiteralExpression))
                    return AnalyzeNode(ifStatement.Statement, warnings, declaredMethods);
                if (ifStatement.Condition.IsKind(SyntaxKind.FalseLiteralExpression))
                    return ifStatement.Else is null ? Complexity.Constant : AnalyzeNode(ifStatement.Else.Statement, warnings, declaredMethods);
                return Complexity.Max(
                    AnalyzeExpressionCosts(ifStatement.Condition, warnings, declaredMethods),
                    AnalyzeNode(ifStatement.Statement, warnings, declaredMethods),
                    ifStatement.Else is null ? Complexity.Constant : AnalyzeNode(ifStatement.Else.Statement, warnings, declaredMethods));
            case SwitchStatementSyntax switchStatement:
                return Complexity.Max(switchStatement.Sections
                    .Select(section => AnalyzeSequence(section.Statements, warnings, declaredMethods))
                    .ToArray());
            case TryStatementSyntax tryStatement:
                return Complexity.Max(
                    AnalyzeNode(tryStatement.Block, warnings, declaredMethods),
                    Complexity.Max(tryStatement.Catches.Select(clause => AnalyzeNode(clause.Block, warnings, declaredMethods)).ToArray()),
                    tryStatement.Finally is null ? Complexity.Constant : AnalyzeNode(tryStatement.Finally.Block, warnings, declaredMethods));
            default:
            {
                var result = AnalyzeExpressionCosts(node, warnings, declaredMethods);
                foreach (var childStatement in node.ChildNodes().OfType<StatementSyntax>())
                    result = Complexity.Max(result, AnalyzeNode(childStatement, warnings, declaredMethods));
                return result;
            }
        }
    }

    private static Complexity AnalyzeLoop(SyntaxNode loop, StatementSyntax body, HashSet<string> warnings, HashSet<string> declaredMethods)
    {
        var condition = loop switch
        {
            ForStatementSyntax statement => statement.Condition,
            WhileStatementSyntax statement => statement.Condition,
            DoStatementSyntax statement => statement.Condition,
            _ => null
        };
        if (loop is not DoStatementSyntax && condition?.IsKind(SyntaxKind.FalseLiteralExpression) == true)
            return Complexity.Constant;

        var bound = GetLoopBound(loop);
        if (bound.Unknown)
            warnings.Add("A loop has no safely recognizable termination or progress condition; its bound is reported as unknown.");
        else if (bound.IsLogarithmic)
            warnings.Add("A logarithmic loop bound is inferred from its update expression; confirm that the value progresses toward termination.");
        var bodyCost = AnalyzeNode(body, warnings, declaredMethods);
        var conditionCost = condition is null ? Complexity.Constant : AnalyzeExpressionCosts(condition, warnings, declaredMethods);
        return bound.Multiply(Complexity.Max(bodyCost, conditionCost));
    }

    private static Complexity GetLoopBound(SyntaxNode loop)
    {
        if (loop is ForEachStatementSyntax or ForEachVariableStatementSyntax)
            return Complexity.Linear;

        var condition = loop switch
        {
            ForStatementSyntax statement => statement.Condition,
            WhileStatementSyntax statement => statement.Condition,
            DoStatementSyntax statement => statement.Condition,
            _ => null
        };
        if (condition is null || condition.IsKind(SyntaxKind.TrueLiteralExpression))
            return Complexity.UnknownComplexity;
        if (condition.IsKind(SyntaxKind.FalseLiteralExpression))
            return Complexity.Constant;

        var updatedIdentifiers = GetUpdatedIdentifiers(loop).ToHashSet(StringComparer.Ordinal);
        var controlVariables = condition.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Select(identifier => identifier.Identifier.ValueText)
            .Where(updatedIdentifiers.Contains)
            .ToHashSet(StringComparer.Ordinal);
        if (controlVariables.Count == 0)
            return Complexity.UnknownComplexity;

        var updates = GetLoopUpdateExpressions(loop)
            .Where(expression => GetUpdatedIdentifiers(expression).Any(controlVariables.Contains))
            .ToArray();
        var update = string.Join(" ", updates.Select(expression => expression.ToString()));
        var bounds = condition.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>()
            .Where(IsComparison)
            .SelectMany(comparison => GetComparedBounds(comparison, controlVariables))
            .ToArray();
        if (bounds.Length == 0)
            return Complexity.UnknownComplexity;

        var bound = Complexity.Max(bounds.Select(boundExpression => EstimateBound(boundExpression)).ToArray());
        var counter = controlVariables.FirstOrDefault();
        var fixedIterations = bound == Complexity.Constant && counter is not null && IsInitializedToConstant(loop, counter);
        if (IsEuclideanReduction(loop, condition, controlVariables))
            return Complexity.Logarithmic;
        if (updates.OfType<AssignmentExpressionSyntax>().Any(assignment => IsFenwickProgress(assignment, controlVariables)))
            return Complexity.Logarithmic;
        if (HasHalvingProgress(loop, controlVariables))
            return fixedIterations ? Complexity.Constant : Complexity.Logarithmic;
        if (ContainsMultiplicativeUpdate(update))
        {
            if (bound == Complexity.Constant && condition is not null &&
                GetInputDerivedBound(condition, controlVariables) != Complexity.Constant)
                return Complexity.Logarithmic;
            return fixedIterations ? Complexity.Constant : Complexity.Logarithmic;
        }

        if (!ContainsUnitProgress(update) && !updates.Any(IsUnitProgressExpression))
            return Complexity.UnknownComplexity;
        return bound == Complexity.Constant && !fixedIterations ? Complexity.Linear : bound;
    }

    private static bool IsComparison(BinaryExpressionSyntax expression) => expression.Kind() is
        SyntaxKind.LessThanExpression or SyntaxKind.LessThanOrEqualExpression or
        SyntaxKind.GreaterThanExpression or SyntaxKind.GreaterThanOrEqualExpression or
        SyntaxKind.NotEqualsExpression;

    private static IEnumerable<ExpressionSyntax> GetComparedBounds(BinaryExpressionSyntax comparison, HashSet<string> controlVariables)
    {
        var leftIsControl = comparison.Left.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(identifier => controlVariables.Contains(identifier.Identifier.ValueText));
        var rightIsControl = comparison.Right.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(identifier => controlVariables.Contains(identifier.Identifier.ValueText));

        if (leftIsControl && !rightIsControl)
            return [comparison.Right];
        if (rightIsControl && !leftIsControl)
            return [comparison.Left];
        return [comparison.Right];
    }

    private static Complexity GetInputDerivedBound(ExpressionSyntax condition, HashSet<string> controlVariables)
    {
        var inferredBounds = condition.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>()
            .Where(IsComparison)
            .SelectMany(comparison => new[] { comparison.Left, comparison.Right })
            .Where(expression => expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                .Any(identifier => controlVariables.Contains(identifier.Identifier.ValueText)))
            .SelectMany(expression => expression.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>())
            .Select(binary =>
            {
                var leftIsControl = binary.Left.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                    .Any(identifier => controlVariables.Contains(identifier.Identifier.ValueText));
                var rightIsControl = binary.Right.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                    .Any(identifier => controlVariables.Contains(identifier.Identifier.ValueText));
                return leftIsControl == rightIsControl
                    ? Complexity.Constant
                    : EstimateBound(leftIsControl ? binary.Right : binary.Left);
            })
            .ToArray();
        return Complexity.Max(inferredBounds);
    }

    private static bool IsCountingSortExpansion(ForStatementSyntax outerLoop)
    {
        var outerCounter = outerLoop.Declaration?.Variables.FirstOrDefault();
        if (outerCounter is null || outerLoop.Condition is not BinaryExpressionSyntax outerCondition ||
            outerCondition.Left is not IdentifierNameSyntax outerIdentifier ||
            outerIdentifier.Identifier.ValueText != outerCounter.Identifier.ValueText ||
            outerCondition.Right is not MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax countsIdentifier,
                Name.Identifier.ValueText: "Length"
            })
            return false;

        var method = outerLoop.Ancestors().OfType<MethodDeclarationSyntax>().FirstOrDefault();
        if (method is null || !method.DescendantNodes().OfType<PostfixUnaryExpressionSyntax>().Any(increment =>
                increment.IsKind(SyntaxKind.PostIncrementExpression) &&
                increment.Operand is ElementAccessExpressionSyntax access &&
                access.Expression is IdentifierNameSyntax arrayName &&
                arrayName.Identifier.ValueText == countsIdentifier.Identifier.ValueText))
            return false;

        var innerLoops = outerLoop.Statement switch
        {
            ForStatementSyntax innerLoop => new[] { innerLoop },
            BlockSyntax { Statements.Count: 1 } block when block.Statements[0] is ForStatementSyntax innerLoop => new[] { innerLoop },
            _ => Array.Empty<ForStatementSyntax>()
        };
        return innerLoops.Any(innerLoop =>
            innerLoop.Declaration?.Variables.FirstOrDefault() is { } innerCounter &&
            innerLoop.Condition is BinaryExpressionSyntax innerCondition &&
            innerCondition.Left is IdentifierNameSyntax innerIdentifier &&
            innerIdentifier.Identifier.ValueText == innerCounter.Identifier.ValueText &&
            innerCondition.Right is ElementAccessExpressionSyntax frequency &&
            frequency.Expression is IdentifierNameSyntax frequencyArray &&
            frequencyArray.Identifier.ValueText == countsIdentifier.Identifier.ValueText &&
            frequency.ArgumentList.Arguments.Any(argument => argument.Expression.DescendantNodesAndSelf()
                .OfType<IdentifierNameSyntax>().Any(identifier => identifier.Identifier.ValueText == outerCounter.Identifier.ValueText)) &&
            innerLoop.Incrementors.Any(IsUnitProgressExpression));
    }

    private static IEnumerable<string> GetUpdatedIdentifiers(SyntaxNode loop)
    {
        foreach (var expression in GetLoopUpdateExpressions(loop))
            foreach (var identifier in GetUpdatedIdentifiers(expression))
                yield return identifier;
    }

    private static IEnumerable<string> GetUpdatedIdentifiers(ExpressionSyntax expression)
    {
        if (expression is PrefixUnaryExpressionSyntax or PostfixUnaryExpressionSyntax &&
            expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>().FirstOrDefault() is { } unaryIdentifier)
            yield return unaryIdentifier.Identifier.ValueText;
        if (expression is AssignmentExpressionSyntax assignment && assignment.Left is IdentifierNameSyntax identifier)
            yield return identifier.Identifier.ValueText;
        if (expression is AssignmentExpressionSyntax { Left: TupleExpressionSyntax tuple })
            foreach (var tupleIdentifier in tuple.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>())
                yield return tupleIdentifier.Identifier.ValueText;
    }

    private static bool IsEuclideanReduction(SyntaxNode loop, ExpressionSyntax? condition, HashSet<string> controlVariables)
    {
        var body = loop switch
        {
            WhileStatementSyntax statement => statement.Statement,
            DoStatementSyntax statement => statement.Statement,
            _ => null
        };
        if (body is null || condition is null ||
            !condition.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>().Any(comparison =>
                IsComparison(comparison) &&
                ((comparison.Left is IdentifierNameSyntax left && controlVariables.Contains(left.Identifier.ValueText) && IsZeroLiteral(comparison.Right)) ||
                 (comparison.Right is IdentifierNameSyntax right && controlVariables.Contains(right.Identifier.ValueText) && IsZeroLiteral(comparison.Left)))))
            return false;

        return body.DescendantNodesAndSelf().OfType<AssignmentExpressionSyntax>().Any(assignment =>
            assignment.Left is TupleExpressionSyntax leftTuple && leftTuple.Arguments.Count >= 2 &&
            leftTuple.Arguments.Any(argument => argument.Expression is IdentifierNameSyntax identifier &&
                                                 controlVariables.Contains(identifier.Identifier.ValueText)) &&
            assignment.Right is TupleExpressionSyntax rightTuple &&
            rightTuple.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>()
                .Any(binary => binary.IsKind(SyntaxKind.ModuloExpression)));
    }

    private static bool IsZeroLiteral(ExpressionSyntax expression) =>
        expression is LiteralExpressionSyntax literal && literal.Token.Value is IConvertible value && value.ToDouble(null) == 0;

    private static bool IsFenwickProgress(AssignmentExpressionSyntax assignment, HashSet<string> controlVariables)
    {
        if ((!assignment.IsKind(SyntaxKind.AddAssignmentExpression) && !assignment.IsKind(SyntaxKind.SubtractAssignmentExpression)) ||
            assignment.Left is not IdentifierNameSyntax variable || !controlVariables.Contains(variable.Identifier.ValueText) ||
            assignment.Right is not BinaryExpressionSyntax { RawKind: (int)SyntaxKind.BitwiseAndExpression } bitwiseAnd)
            return false;

        var leftUsesVariable = bitwiseAnd.Left.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(identifier => identifier.Identifier.ValueText == variable.Identifier.ValueText);
        var rightUsesNegatedVariable = bitwiseAnd.Right is PrefixUnaryExpressionSyntax
            {
                RawKind: (int)SyntaxKind.UnaryMinusExpression,
                Operand: IdentifierNameSyntax negatedVariable
            } && negatedVariable.Identifier.ValueText == variable.Identifier.ValueText;
        var rightUsesVariable = bitwiseAnd.Right.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(identifier => identifier.Identifier.ValueText == variable.Identifier.ValueText);
        var leftIsNegatedVariable = bitwiseAnd.Left is PrefixUnaryExpressionSyntax
            {
                RawKind: (int)SyntaxKind.UnaryMinusExpression,
                Operand: IdentifierNameSyntax negatedLeftVariable
            } && negatedLeftVariable.Identifier.ValueText == variable.Identifier.ValueText;
        return (leftUsesVariable && rightUsesNegatedVariable) || (rightUsesVariable && leftIsNegatedVariable);
    }

    private static IEnumerable<ExpressionSyntax> GetLoopUpdateExpressions(SyntaxNode loop)
    {
        if (loop is ForStatementSyntax forStatement)
            return forStatement.Incrementors;

        var body = loop switch
        {
            WhileStatementSyntax statement => statement.Statement,
            DoStatementSyntax statement => statement.Statement,
            _ => null
        };
        if (body is null)
            return [];

        return body.DescendantNodesAndSelf().OfType<ExpressionSyntax>()
            .Where(expression => expression is AssignmentExpressionSyntax or PrefixUnaryExpressionSyntax or PostfixUnaryExpressionSyntax)
            .Where(expression => !expression.Ancestors().TakeWhile(ancestor => ancestor != body)
                .Any(ancestor => ancestor is ForStatementSyntax or ForEachStatementSyntax or WhileStatementSyntax or DoStatementSyntax));
    }

    private static Complexity EstimateBound(ExpressionSyntax expression)
    {
        if (IsNumericLiteral(expression))
            return Complexity.Constant;
        if (expression is ParenthesizedExpressionSyntax parenthesized)
            return EstimateBound(parenthesized.Expression);
        if (expression is BinaryExpressionSyntax binary)
        {
            var left = EstimateBound(binary.Left);
            var right = EstimateBound(binary.Right);
            return binary.IsKind(SyntaxKind.MultiplyExpression)
                ? left.Multiply(right)
                : Complexity.Max(left, right);
        }
        return expression is IdentifierNameSyntax or MemberAccessExpressionSyntax
            ? Complexity.Linear
            : expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>().Any()
                ? Complexity.Linear
                : Complexity.Constant;
    }

    private static bool IsInitializedToConstant(SyntaxNode loop, string variableName)
    {
        if (loop is ForStatementSyntax forStatement)
        {
            var declared = forStatement.Declaration?.Variables.FirstOrDefault(variable => variable.Identifier.ValueText == variableName);
            if (declared?.Initializer?.Value is { } declaredInitializer)
                return IsNumericLiteral(declaredInitializer);
            var assignment = forStatement.Initializers.OfType<AssignmentExpressionSyntax>()
                .FirstOrDefault(initializer => initializer.Left is IdentifierNameSyntax identifier && identifier.Identifier.ValueText == variableName);
            if (assignment is not null)
                return IsNumericLiteral(assignment.Right);
        }

        var method = loop.Ancestors().OfType<MethodDeclarationSyntax>().FirstOrDefault();
        var local = method?.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(variable => variable.Identifier.ValueText == variableName && variable.SpanStart < loop.SpanStart)
            .OrderByDescending(variable => variable.SpanStart)
            .FirstOrDefault();
        return local?.Initializer?.Value is { } initializerValue && IsNumericLiteral(initializerValue);
    }

    private static bool IsNumeric(object value) => value is byte or sbyte or short or ushort or int or uint or long or ulong or float or double or decimal;

    private static bool ContainsMultiplicativeUpdate(string update) =>
        update.Contains("*=", StringComparison.Ordinal) || update.Contains("/=", StringComparison.Ordinal) ||
        update.Contains(" = ", StringComparison.Ordinal) && (update.Contains(" * ", StringComparison.Ordinal) || update.Contains(" / ", StringComparison.Ordinal));

    private static bool ContainsUnitProgress(string update) =>
        update.Contains("++", StringComparison.Ordinal) || update.Contains("--", StringComparison.Ordinal) ||
        update.Contains("+=", StringComparison.Ordinal) || update.Contains("-=", StringComparison.Ordinal);

    private static bool IsUnitProgressExpression(ExpressionSyntax expression)
    {
        if (expression is PrefixUnaryExpressionSyntax or PostfixUnaryExpressionSyntax &&
            expression.Kind() is SyntaxKind.PreIncrementExpression or SyntaxKind.PreDecrementExpression or
                SyntaxKind.PostIncrementExpression or SyntaxKind.PostDecrementExpression)
            return true;
        if (expression is not AssignmentExpressionSyntax assignment ||
            assignment.Left is not IdentifierNameSyntax variable)
            return false;
        if (assignment.IsKind(SyntaxKind.AddAssignmentExpression) || assignment.IsKind(SyntaxKind.SubtractAssignmentExpression))
            return true;
        return assignment.Right is BinaryExpressionSyntax binary &&
            (binary.IsKind(SyntaxKind.AddExpression) || binary.IsKind(SyntaxKind.SubtractExpression)) &&
            ((binary.Left is IdentifierNameSyntax updatedVariable && updatedVariable.Identifier.ValueText == variable.Identifier.ValueText && IsNumericLiteral(binary.Right)) ||
             (binary.Right is IdentifierNameSyntax otherUpdatedVariable && otherUpdatedVariable.Identifier.ValueText == variable.Identifier.ValueText && IsNumericLiteral(binary.Left)));
    }

    private static bool HasHalvingProgress(SyntaxNode loop, HashSet<string> controlVariables)
    {
        var body = loop switch
        {
            WhileStatementSyntax statement => statement.Statement,
            DoStatementSyntax statement => statement.Statement,
            ForStatementSyntax statement => statement.Statement,
            _ => null
        };
        if (body is null)
            return false;

        var halvedVariables = body.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(variable => IsHalvingExpression(variable.Initializer?.Value))
            .Select(variable => variable.Identifier.ValueText)
            .Concat(body.DescendantNodes().OfType<AssignmentExpressionSyntax>()
                .Where(assignment => assignment.Left is IdentifierNameSyntax && IsHalvingExpression(assignment.Right))
                .Select(assignment => ((IdentifierNameSyntax)assignment.Left).Identifier.ValueText))
            .ToHashSet(StringComparer.Ordinal);

        return body.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(assignment =>
            assignment.Left is IdentifierNameSyntax left && controlVariables.Contains(left.Identifier.ValueText) &&
            assignment.Right.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                .Any(identifier => halvedVariables.Contains(identifier.Identifier.ValueText)));
    }

    private static bool IsHalvingExpression(ExpressionSyntax? expression) => expression?.DescendantNodesAndSelf()
        .OfType<BinaryExpressionSyntax>()
        .Any(binary => binary.IsKind(SyntaxKind.DivideExpression) && IsNumericLiteral(binary.Right) &&
                       binary.Right is LiteralExpressionSyntax literal && Convert.ToDouble(literal.Token.Value) == 2 ||
                       binary.IsKind(SyntaxKind.RightShiftExpression) && IsNumericLiteral(binary.Right) &&
                       binary.Right is LiteralExpressionSyntax shift && Convert.ToDouble(shift.Token.Value) == 1) == true;

    private static Complexity AnalyzeExpressionCosts(SyntaxNode node, HashSet<string> warnings, HashSet<string> declaredMethods)
    {
        var result = Complexity.Constant;
        foreach (var array in node.DescendantNodesAndSelf().OfType<ArrayCreationExpressionSyntax>())
            result = Complexity.Max(result, GetArraySizeComplexity(array));
        foreach (var creation in node.DescendantNodesAndSelf().OfType<ObjectCreationExpressionSyntax>())
            result = Complexity.Max(result, GetCollectionCreationComplexity(creation));

        foreach (var invocation in node.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>())
        {
            var name = GetInvokedName(invocation);
            var operation = IsConstantTimeMathOperation(invocation) || invocation.Expression is not MemberAccessExpressionSyntax
                ? Complexity.Constant
                : name switch
            {
                "Sort" or "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" => Complexity.Linearithmic,
                "BinarySearch" => Complexity.Logarithmic,
                _ when LinearOperations.Contains(name) => Complexity.Linear,
                "ForEach" => Complexity.Linear,
                _ => Complexity.Constant
            };
            result = Complexity.Max(result, operation);
            if (declaredMethods.Contains(name))
                warnings.Add($"Helper method '{name}' is not interprocedurally analyzed; its cost may be missing.");
        }
        return result;
    }

    private static bool IsConstantTimeMathOperation(InvocationExpressionSyntax invocation) =>
        invocation.Expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax typeName,
            Name.Identifier.ValueText: "Min" or "Max"
        } && typeName.Identifier.ValueText is "Math" or "MathF";

    private static string GetInvokedName(InvocationExpressionSyntax invocation) => invocation.Expression switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        GenericNameSyntax generic => generic.Identifier.ValueText,
        _ => string.Empty
    };

    private static bool HasUnanalyzedHelperCalls(SyntaxNode body, string currentMethod, HashSet<string> declaredMethods) =>
        body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Any(invocation => GetInvokedName(invocation) is var name && name != currentMethod && declaredMethods.Contains(name));

    private static bool TryRecognizeDijkstra(SyntaxNode root)
    {
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>();
        return methods.Any(method =>
        {
            if (!method.Identifier.ValueText.Contains("Dijkstra", StringComparison.OrdinalIgnoreCase) || method.Body is null)
                return false;

            var nodes = method.Body.DescendantNodesAndSelf();
            var hasPriorityQueue = nodes.OfType<GenericNameSyntax>()
                .Any(name => name.Identifier.ValueText == "PriorityQueue");
            var hasEnqueue = nodes.OfType<InvocationExpressionSyntax>()
                .Any(invocation => GetInvokedName(invocation) == "Enqueue");
            var hasStaleEntryGuard = nodes.OfType<IfStatementSyntax>().Any(statement =>
                statement.Condition.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>()
                    .Any(binary => binary.IsKind(SyntaxKind.NotEqualsExpression) ||
                                   binary.IsKind(SyntaxKind.GreaterThanExpression) ||
                                   binary.IsKind(SyntaxKind.GreaterThanOrEqualExpression)) &&
                statement.Statement.DescendantNodesAndSelf().OfType<ContinueStatementSyntax>().Any());
            var hasQueueDrainLoop = nodes.OfType<WhileStatementSyntax>().Any(loop =>
                loop.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                    .Any(invocation => GetInvokedName(invocation) is "TryDequeue" or "Dequeue"));
            var hasAdjacencyTraversal = nodes.OfType<ForEachStatementSyntax>().Any(statement =>
                statement.Expression.DescendantNodesAndSelf().OfType<ElementAccessExpressionSyntax>().Any());
            var hasUnanalyzedHelperCalls = nodes.OfType<InvocationExpressionSyntax>().Any(invocation =>
                methods.Any(candidate => candidate.Identifier.ValueText == GetInvokedName(invocation) &&
                                         candidate.Identifier.ValueText != method.Identifier.ValueText));

            return hasPriorityQueue && hasEnqueue && hasStaleEntryGuard && hasQueueDrainLoop &&
                   hasAdjacencyTraversal && !hasUnanalyzedHelperCalls;
        });
    }

    private static bool TryRecognizeHeapSort(SyntaxNode root, out string auxiliarySpace)
    {
        auxiliarySpace = "O(1)";
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>().ToArray();
        var siftDownMethods = methods.Where(method =>
            method.Identifier.ValueText.Contains("SiftDown", StringComparison.OrdinalIgnoreCase) && method.Body is not null).ToArray();
        if (siftDownMethods.Length == 0)
            return false;

        var heapifyMethods = methods.Where(method =>
            (method.Identifier.ValueText.Contains("Heapify", StringComparison.OrdinalIgnoreCase) ||
             method.Identifier.ValueText.Contains("BuildHeap", StringComparison.OrdinalIgnoreCase)) && method.Body is not null).ToArray();
        var sortMethod = methods.FirstOrDefault(method => method.Body is not null &&
            (method.Identifier.ValueText.Contains("HeapSort", StringComparison.OrdinalIgnoreCase) ||
             heapifyMethods.Any(heapify => method.Body.DescendantNodes().OfType<InvocationExpressionSyntax>()
                 .Any(invocation => GetInvokedName(invocation) == heapify.Identifier.ValueText)) &&
             siftDownMethods.Any(siftDown => method.Body.DescendantNodes().OfType<InvocationExpressionSyntax>()
                 .Any(invocation => GetInvokedName(invocation) == siftDown.Identifier.ValueText))));
        if (sortMethod?.Body is null || !sortMethod.ParameterList.Parameters.Any(parameter => parameter.Type is ArrayTypeSyntax))
            return false;

        var heapMethods = siftDownMethods.Concat(heapifyMethods).Append(sortMethod).Distinct().ToArray();
        if (heapMethods.Any(method => method.Body!.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                .Any(invocation => methods.Any(candidate => candidate.Identifier.ValueText == GetInvokedName(invocation)) &&
                                   !heapMethods.Any(candidate => candidate.Identifier.ValueText == GetInvokedName(invocation)))))
            return false;

        if (heapMethods.Any(method => method.Body!.DescendantNodesAndSelf().OfType<ArrayCreationExpressionSyntax>().Any() ||
                                      method.Body.DescendantNodesAndSelf().OfType<ObjectCreationExpressionSyntax>().Any()))
            return false;

        if (heapMethods.Any(method => method.Body!.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                .Any(invocation => GetInvokedName(invocation) == method.Identifier.ValueText)))
            auxiliarySpace = "O(log n)";
        return true;
    }

    private static bool TryRecognizeTopologicalSort(SyntaxNode root)
    {
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>().ToArray();
        return methods.Any(method =>
        {
            if (!method.Identifier.ValueText.Contains("Topological", StringComparison.OrdinalIgnoreCase) || method.Body is null)
                return false;

            var nodes = method.Body.DescendantNodesAndSelf();
            var hasQueue = nodes.OfType<GenericNameSyntax>().Any(name => name.Identifier.ValueText == "Queue");
            var hasEnqueue = nodes.OfType<InvocationExpressionSyntax>()
                .Any(invocation => GetInvokedName(invocation) == "Enqueue");
            var hasDequeueLoop = nodes.OfType<WhileStatementSyntax>().Any(loop =>
                loop.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                    .Any(invocation => GetInvokedName(invocation) == "Dequeue"));
            var hasAdjacencyTraversal = nodes.OfType<ForEachStatementSyntax>().Any(statement =>
                statement.Expression.DescendantNodesAndSelf().OfType<ElementAccessExpressionSyntax>().Any());
            var hasIndegree = nodes.OfType<IdentifierNameSyntax>()
                .Any(identifier => identifier.Identifier.ValueText.Contains("indegree", StringComparison.OrdinalIgnoreCase));
            var callsHelper = nodes.OfType<InvocationExpressionSyntax>().Any(invocation =>
                methods.Any(candidate => candidate.Identifier.ValueText == GetInvokedName(invocation) &&
                                         candidate.Identifier.ValueText != method.Identifier.ValueText));

            return hasQueue && hasEnqueue && hasDequeueLoop && hasAdjacencyTraversal && hasIndegree && !callsHelper;
        });
    }

    private static bool TryRecognizeAdditionalAlgorithm(SyntaxNode root, out RecognizedAlgorithm estimate)
    {
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>().ToArray();
        foreach (var method in methods)
        {
            if (method.Body is null)
                continue;

            var nodes = method.Body.DescendantNodesAndSelf();
            if (method.Identifier.ValueText.Contains("TernarySearch", StringComparison.OrdinalIgnoreCase) &&
                nodes.OfType<WhileStatementSyntax>().Any() &&
                nodes.OfType<BinaryExpressionSyntax>().Any(binary => binary.IsKind(SyntaxKind.DivideExpression) && IsNumericLiteral(binary.Right) &&
                    binary.Right is LiteralExpressionSyntax literal && Convert.ToDouble(literal.Token.Value) == 3) &&
                nodes.OfType<ElementAccessExpressionSyntax>().Count() >= 2)
            {
                estimate = new RecognizedAlgorithm("O(log n)", "O(1)", "A ternary-search interval reduction was recognized.",
                    "Ternary search assumes a sorted search space and a constant number of comparisons per iteration.",
                    "The ternary-search pattern is inferred syntactically; sortedness and update correctness are not verified.");
                return true;
            }

            if (method.Identifier.ValueText.Contains("InterpolationSearch", StringComparison.OrdinalIgnoreCase) &&
                nodes.OfType<WhileStatementSyntax>().Any() &&
                nodes.OfType<BinaryExpressionSyntax>().Any(binary => binary.IsKind(SyntaxKind.MultiplyExpression)) &&
                nodes.OfType<ElementAccessExpressionSyntax>().Count() >= 2)
            {
                estimate = new RecognizedAlgorithm("O(n)", "O(1)", "Interpolation search was recognized using its worst-case bound.",
                    "The displayed interpolation-search time is worst case; average O(log log n) requires uniformly distributed sorted keys.",
                    "The interpolation-search pattern is inferred syntactically; data distribution and update correctness are not verified.");
                return true;
            }

            if (method.Identifier.ValueText.Contains("JumpSearch", StringComparison.OrdinalIgnoreCase) &&
                nodes.OfType<InvocationExpressionSyntax>().Any(invocation =>
                    invocation.Expression is MemberAccessExpressionSyntax member && member.Name.Identifier.ValueText == "Sqrt") &&
                nodes.OfType<WhileStatementSyntax>().Any() && nodes.OfType<ForStatementSyntax>().Any() &&
                nodes.OfType<ElementAccessExpressionSyntax>().Any())
            {
                estimate = new RecognizedAlgorithm("O(sqrt n)", "O(1)", "A square-root jump-search block scan was recognized.",
                    "Jump search assumes sorted input and jump size proportional to sqrt(n).",
                    "The jump-search pattern is inferred syntactically; sortedness and jump-size correctness are not verified.");
                return true;
            }

            if (method.Identifier.ValueText.Contains("Prim", StringComparison.OrdinalIgnoreCase) &&
                nodes.OfType<GenericNameSyntax>().Any(name => name.Identifier.ValueText == "PriorityQueue") &&
                nodes.OfType<InvocationExpressionSyntax>().Any(invocation => GetInvokedName(invocation) == "Enqueue") &&
                nodes.OfType<WhileStatementSyntax>().Any(loop => loop.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                    .Any(invocation => GetInvokedName(invocation) is "TryDequeue" or "Dequeue")) &&
                nodes.OfType<ForEachStatementSyntax>().Any(statement => statement.Expression.DescendantNodesAndSelf()
                    .OfType<ElementAccessExpressionSyntax>().Any()) &&
                nodes.OfType<ArrayCreationExpressionSyntax>().Any(array => array.Type.ElementType.ToString() == "bool") &&
                nodes.OfType<ContinueStatementSyntax>().Any())
            {
                estimate = new RecognizedAlgorithm("O((V + E) log E)", "O(V + E)", "A lazy-priority-queue Prim traversal was recognized.",
                    "Prim's bounds assume an adjacency-list graph and a binary heap that may store multiple edge candidates; input graph storage is excluded from auxiliary space.",
                    "The Prim pattern is inferred syntactically; graph connectivity and MST correctness are not verified.");
                return true;
            }

            if (TryRecognizeSieve(method, nodes))
            {
                estimate = new RecognizedAlgorithm("O(n log log n)", "O(n)", "A sieve marking multiples from each prime square was recognized.",
                    "Sieve space includes the Boolean table through the input limit.",
                    "The sieve pattern is inferred syntactically; prime-marking and boundary correctness are not verified.");
                return true;
            }
        }

        estimate = default;
        return false;
    }

    private static bool TryRecognizeSieve(MethodDeclarationSyntax method, IEnumerable<SyntaxNode> nodes)
    {
        if (!method.Identifier.ValueText.Contains("Sieve", StringComparison.OrdinalIgnoreCase) ||
            !nodes.OfType<ArrayCreationExpressionSyntax>().Any())
            return false;

        var loops = nodes.OfType<ForStatementSyntax>().ToArray();
        return loops.Any(outer => outer.Condition?.DescendantNodesAndSelf().OfType<BinaryExpressionSyntax>()
                   .Any(binary => binary.IsKind(SyntaxKind.MultiplyExpression)) == true &&
               loops.Any(inner => inner.Ancestors().Contains(outer) &&
                   inner.Incrementors.OfType<AssignmentExpressionSyntax>().Any(assignment =>
                       assignment.IsKind(SyntaxKind.AddAssignmentExpression) &&
                       assignment.Right is IdentifierNameSyntax prime &&
                       outer.Declaration?.Variables.Any(variable => variable.Identifier.ValueText == prime.Identifier.ValueText) == true)));
    }

    private static int GetRecursiveCallsPerPath(SyntaxNode node, string methodName)
    {
        switch (node)
        {
            case InvocationExpressionSyntax invocation:
                return (GetInvokedName(invocation) == methodName ? 1 : 0) +
                       invocation.ArgumentList.Arguments.Sum(argument => GetRecursiveCallsPerPath(argument, methodName));
            case IfStatementSyntax ifStatement:
                return GetRecursiveCallsPerPath(ifStatement.Condition, methodName) +
                       Math.Max(GetRecursiveCallsPerPath(ifStatement.Statement, methodName),
                           ifStatement.Else is null ? 0 : GetRecursiveCallsPerPath(ifStatement.Else.Statement, methodName));
            case ConditionalExpressionSyntax conditional:
                return GetRecursiveCallsPerPath(conditional.Condition, methodName) +
                       Math.Max(GetRecursiveCallsPerPath(conditional.WhenTrue, methodName),
                           GetRecursiveCallsPerPath(conditional.WhenFalse, methodName));
            case SwitchStatementSyntax switchStatement:
                return GetRecursiveCallsPerPath(switchStatement.Expression, methodName) +
                       (switchStatement.Sections.Select(section => section.Statements.Sum(statement =>
                           GetRecursiveCallsPerPath(statement, methodName))).DefaultIfEmpty(0).Max());
            case BlockSyntax block:
                return block.Statements.Sum(statement => GetRecursiveCallsPerPath(statement, methodName));
            default:
                return node.ChildNodes().Sum(child => GetRecursiveCallsPerPath(child, methodName));
        }
    }

    private static bool HasRecursiveCallInLoop(SyntaxNode body, string methodName, out bool unknownLoopBound)
    {
        unknownLoopBound = false;
        var foundInputBound = false;
        foreach (var invocation in body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                     .Where(invocation => GetInvokedName(invocation) == methodName))
        {
            foreach (var loop in invocation.Ancestors().Where(IsLoopStatement))
            {
                var bound = GetLoopBound(loop);
                if (bound.Unknown)
                    unknownLoopBound = true;
                else if (bound != Complexity.Constant)
                    foundInputBound = true;
            }
        }
        return foundInputBound;
    }

    private static Complexity EstimateRecursion(MethodDeclarationSyntax method, int recursiveCallsPerPath, bool recursiveCallInLoop, bool unknownLoopBound, Complexity localWork, HashSet<string> warnings, HashSet<string> assumptions)
    {
        warnings.Add($"Recursive method '{method.Identifier.ValueText}' is estimated from its apparent argument reduction; termination and recurrence behavior are not proven.");
        assumptions.Add("Recursive calls are classified syntactically; mutual recursion, memoization, and nonstandard recurrences are not fully modeled.");

        if (localWork.Unknown || unknownLoopBound)
            return Complexity.UnknownComplexity;

        if (HasHalvingReduction(method))
        {
            if (recursiveCallInLoop)
                return Complexity.UnknownComplexity;
            if (recursiveCallsPerPath > 1)
                return localWork.Degree > 0 ? Complexity.Linearithmic : Complexity.Linear;
            return localWork.Degree > 0 ? localWork : Complexity.Logarithmic;
        }

        if (HasLinearReduction(method))
        {
            if (recursiveCallInLoop)
                return Complexity.FactorialComplexity;
            if (recursiveCallsPerPath > 1)
                return Complexity.ExponentialComplexity;
            return localWork.Degree > 0 ? Complexity.Linear.Multiply(localWork) : Complexity.Linear;
        }

        warnings.Add($"The recursive reduction in '{method.Identifier.ValueText}' is not recognized; time complexity is reported as unknown.");
        return Complexity.UnknownComplexity;
    }

    private static bool HasHalvingReduction(MethodDeclarationSyntax method)
    {
        var body = method.Body ?? (SyntaxNode?)method.ExpressionBody;
        if (body is null)
            return false;

        var halvedVariables = body.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(variable => IsHalvingExpression(variable.Initializer?.Value))
            .Select(variable => variable.Identifier.ValueText)
            .Concat(body.DescendantNodes().OfType<AssignmentExpressionSyntax>()
                .Where(assignment => IsHalvingExpression(assignment.Right) && assignment.Left is IdentifierNameSyntax)
                .Select(assignment => ((IdentifierNameSyntax)assignment.Left).Identifier.ValueText))
            .ToHashSet(StringComparer.Ordinal);

        return body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Where(invocation => GetInvokedName(invocation) == method.Identifier.ValueText)
            .Any(invocation => invocation.ArgumentList.Arguments.Any(argument =>
                IsHalvingExpression(argument.Expression) || argument.Expression.DescendantNodesAndSelf()
                    .OfType<IdentifierNameSyntax>().Any(identifier => halvedVariables.Contains(identifier.Identifier.ValueText))));
    }

    private static bool HasLinearReduction(MethodDeclarationSyntax method)
    {
        var body = method.Body ?? (SyntaxNode?)method.ExpressionBody;
        if (body is null)
            return false;

        var parameters = method.ParameterList.Parameters.Select(parameter => parameter.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        return body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Where(invocation => GetInvokedName(invocation) == method.Identifier.ValueText)
            .SelectMany(invocation => invocation.ArgumentList.Arguments)
            .Select(argument => argument.Expression)
            .OfType<BinaryExpressionSyntax>()
            .Any(binary => (binary.IsKind(SyntaxKind.SubtractExpression) || binary.IsKind(SyntaxKind.AddExpression)) &&
                           binary.Left is IdentifierNameSyntax identifier && parameters.Contains(identifier.Identifier.ValueText) &&
                           IsNumericLiteral(binary.Right));
    }

    private static Complexity AnalyzeSpace(SyntaxNode body, HashSet<string> warnings)
    {
        var result = Complexity.Constant;
        foreach (var array in body.DescendantNodes().OfType<ArrayCreationExpressionSyntax>())
        {
            var retainedAcrossIterations = IsAllocationRetained(array);
            var loopMultiplier = retainedAcrossIterations ? GetEnclosingLoopMultiplier(array, warnings) : Complexity.Constant;
            if (retainedAcrossIterations && loopMultiplier != Complexity.Constant)
                warnings.Add("Array allocations inside loops are assumed to remain live when estimating auxiliary space.");
            result = Complexity.Max(result, GetArraySizeComplexity(array).Multiply(loopMultiplier));
        }
        foreach (var creation in body.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            var retainedAcrossIterations = IsAllocationRetained(creation);
            var loopMultiplier = retainedAcrossIterations ? GetEnclosingLoopMultiplier(creation, warnings) : Complexity.Constant;
            var collectionSpace = GetCollectionCreationComplexity(creation);
            if (retainedAcrossIterations && loopMultiplier != Complexity.Constant && collectionSpace != Complexity.Constant)
                warnings.Add("Collection allocations inside loops are assumed to remain live when estimating auxiliary space.");
            result = Complexity.Max(result, collectionSpace.Multiply(loopMultiplier));
        }

        foreach (var invocation in body.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var name = GetInvokedName(invocation);
            if (invocation.Expression is MemberAccessExpressionSyntax &&
                name is "ToList" or "ToArray" or "ToDictionary" or "ToLookup" or "GroupBy" or "Distinct" or
                "Union" or "Intersect" or "Except" or "Reverse" or "OrderBy" or "OrderByDescending")
            {
                var loopMultiplier = GetEnclosingLoopMultiplier(invocation, warnings);
                if (loopMultiplier != Complexity.Constant)
                    warnings.Add("Materialized query results inside loops are assumed to remain live when estimating auxiliary space.");
                result = Complexity.Max(result, Complexity.Linear.Multiply(loopMultiplier));
            }
            if (name is "Add" or "AddRange" or "Enqueue" or "Push" && IsInsideLoop(invocation))
            {
                result = Complexity.Max(result, GetEnclosingLoopMultiplier(invocation, warnings));
                warnings.Add("Collection growth inside loops assumes inserted items remain live; transient allocations may use less peak space.");
            }
        }

        if (body.DescendantNodes().OfType<StackAllocArrayCreationExpressionSyntax>().Any())
            warnings.Add("Stack allocation size is not incorporated into auxiliary-space growth estimates.");
        return result;
    }

    private static bool IsAllocationRetained(SyntaxNode allocation)
    {
        if (allocation.Parent is EqualsValueClauseSyntax &&
            allocation.Parent.Parent is VariableDeclaratorSyntax variable)
            return IsStoredAcrossIterations(variable, allocation);
        if (allocation.Parent is AssignmentExpressionSyntax assignment)
            return assignment.Left is not IdentifierNameSyntax;
        if (allocation.Parent is ArgumentSyntax argument &&
            argument.Parent?.Parent is InvocationExpressionSyntax invocation &&
            GetInvokedName(invocation) is "Add" or "AddRange" or "Enqueue" or "Push")
            return true;
        return true;
    }

    private static bool IsStoredAcrossIterations(VariableDeclaratorSyntax variable, SyntaxNode allocation)
    {
        var loop = allocation.Ancestors().FirstOrDefault(IsLoopStatement);
        if (loop is null)
            return false;

        var loopBody = loop switch
        {
            ForStatementSyntax statement => statement.Statement,
            ForEachStatementSyntax statement => statement.Statement,
            ForEachVariableStatementSyntax statement => statement.Statement,
            WhileStatementSyntax statement => statement.Statement,
            DoStatementSyntax statement => statement.Statement,
            _ => null
        };
        if (loopBody is null)
            return false;

        var name = variable.Identifier.ValueText;
        return loopBody.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>().Any(invocation =>
                   GetInvokedName(invocation) is "Add" or "AddRange" or "Enqueue" or "Push" &&
                   invocation.ArgumentList.Arguments.Any(argument => argument.Expression.DescendantNodesAndSelf()
                       .OfType<IdentifierNameSyntax>().Any(identifier => identifier.Identifier.ValueText == name))) ||
               loopBody.DescendantNodesAndSelf().OfType<AssignmentExpressionSyntax>().Any(assignment =>
                   assignment.Left is not IdentifierNameSyntax && assignment.Right.DescendantNodesAndSelf()
                       .OfType<IdentifierNameSyntax>().Any(identifier => identifier.Identifier.ValueText == name));
    }

    private static bool IsInsideLoop(SyntaxNode node) => node.Ancestors().Any(ancestor => ancestor is ForStatementSyntax or ForEachStatementSyntax or WhileStatementSyntax or DoStatementSyntax);

    private static Complexity GetEnclosingLoopMultiplier(SyntaxNode node, HashSet<string> warnings)
    {
        var result = Complexity.Constant;
        foreach (var loop in node.Ancestors().Where(IsLoopStatement))
        {
            var bound = GetLoopBound(loop);
            if (bound.Unknown)
                warnings.Add("Space allocated inside a loop with an unknown bound cannot be estimated reliably.");
            result = result.Multiply(bound);
        }
        return result;
    }

    private static bool IsLoopStatement(SyntaxNode node) => node is
        ForStatementSyntax or ForEachStatementSyntax or ForEachVariableStatementSyntax or WhileStatementSyntax or DoStatementSyntax;

    private static Complexity GetArraySizeComplexity(ArrayCreationExpressionSyntax array) =>
        array.Type.RankSpecifiers.SelectMany(rank => rank.Sizes)
            .Where(size => size is not OmittedArraySizeExpressionSyntax)
            .Aggregate(Complexity.Constant, (total, size) => total.Multiply(EstimateBound(size)));

    private static Complexity GetCollectionCreationComplexity(ObjectCreationExpressionSyntax creation)
    {
        var typeName = creation.Type.DescendantNodesAndSelf().OfType<SimpleNameSyntax>().LastOrDefault()?.Identifier.ValueText;
        if (typeName is not ("List" or "Dictionary" or "HashSet" or "Queue" or "Stack" or "LinkedList" or
            "SortedSet" or "SortedDictionary" or "StringBuilder") || creation.ArgumentList?.Arguments.FirstOrDefault()?.Expression is not { } size)
            return Complexity.Constant;
        return EstimateBound(size);
    }

    private static bool IsNumericLiteral(ExpressionSyntax expression) =>
        expression is LiteralExpressionSyntax literal && IsNumeric(literal.Token.Value!);

    private readonly record struct RecognizedAlgorithm(string Time, string Space, string Explanation, string Assumption, string Warning);

    private readonly record struct Complexity(int Degree, int LogarithmicPower, bool Exponential = false, bool Factorial = false, bool Unknown = false)
    {
        public bool IsLogarithmic => LogarithmicPower > 0 && Degree == 0;

        public static Complexity Constant => new(0, 0);
        public static Complexity Linear => new(1, 0);
        public static Complexity Logarithmic => new(0, 1);
        public static Complexity Linearithmic => new(1, 1);
        public static Complexity ExponentialComplexity => new(0, 0, Exponential: true);
        public static Complexity FactorialComplexity => new(0, 0, Factorial: true);
        public static Complexity UnknownComplexity => new(0, 0, Unknown: true);

        public Complexity Multiply(Complexity other) => new(
            Degree + other.Degree,
            LogarithmicPower + other.LogarithmicPower,
            Exponential || other.Exponential,
            Factorial || other.Factorial,
            Unknown || other.Unknown);

        public static Complexity Max(params Complexity[] values)
        {
            if (values.Length == 0)
                return Constant;
            if (values.Any(value => value.Unknown))
                return UnknownComplexity;
            return values.Aggregate((left, right) => Compare(left, right) >= 0 ? left : right);
        }

        private static int Compare(Complexity left, Complexity right)
        {
            if (left.Factorial != right.Factorial)
                return left.Factorial ? 1 : -1;
            if (left.Exponential != right.Exponential)
                return left.Exponential ? 1 : -1;
            if (left.Degree != right.Degree)
                return left.Degree.CompareTo(right.Degree);
            return left.LogarithmicPower.CompareTo(right.LogarithmicPower);
        }

        public string ToBigO()
        {
            if (Unknown)
                return "Unknown (input-dependent)";
            if (Factorial)
                return Degree == 0 ? "O(n!)" : $"O(n^{Degree} n!)";
            if (Exponential)
                return "O(2^n)";
            if (Degree == 0 && LogarithmicPower == 0)
                return "O(1)";
            var parts = new List<string>();
            if (Degree > 0)
                parts.Add(Degree == 1 ? "n" : $"n^{Degree}");
            if (LogarithmicPower > 0)
                parts.Add(LogarithmicPower == 1 ? "log n" : $"(log n)^{LogarithmicPower}");
            return $"O({string.Join(" ", parts)})";
        }
    }
}
