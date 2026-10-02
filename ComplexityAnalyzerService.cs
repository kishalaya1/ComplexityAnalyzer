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
            var methodTime = AnalyzeNode(body, warnings, declaredMethods);
            var recursiveCalls = body.DescendantNodes().OfType<InvocationExpressionSyntax>()
                .Count(invocation => GetInvokedName(invocation) == method.Identifier.ValueText);

            if (recursiveCalls > 0)
            {
                methodTime = EstimateRecursion(method, recursiveCalls, warnings, assumptions);
                var recursiveStack = HasHalvingReduction(body) ? Complexity.Logarithmic : Complexity.Linear;
                space = Complexity.Max(space, recursiveStack);
            }

            time = Complexity.Max(time, methodTime);
            space = Complexity.Max(space, AnalyzeSpace(body, warnings));
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
        return bound.Multiply(AnalyzeNode(body, warnings, declaredMethods));
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
        if (ContainsMultiplicativeUpdate(update))
            return fixedIterations ? Complexity.Constant : Complexity.Logarithmic;

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
        if (expression is not AssignmentExpressionSyntax assignment ||
            assignment.Left is not IdentifierNameSyntax variable)
            return false;
        if (assignment.IsKind(SyntaxKind.AddAssignmentExpression) || assignment.IsKind(SyntaxKind.SubtractAssignmentExpression))
            return true;
        return assignment.Right is BinaryExpressionSyntax binary &&
            (binary.IsKind(SyntaxKind.AddExpression) || binary.IsKind(SyntaxKind.SubtractExpression)) &&
            binary.Left is IdentifierNameSyntax updatedVariable && updatedVariable.Identifier.ValueText == variable.Identifier.ValueText &&
            IsNumericLiteral(binary.Right);
    }

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
            var operation = name switch
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

    private static string GetInvokedName(InvocationExpressionSyntax invocation) => invocation.Expression switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        GenericNameSyntax generic => generic.Identifier.ValueText,
        _ => string.Empty
    };

    private static Complexity EstimateRecursion(MethodDeclarationSyntax method, int recursiveCalls, HashSet<string> warnings, HashSet<string> assumptions)
    {
        var body = method.Body?.ToString() ?? method.ExpressionBody?.ToString() ?? string.Empty;
        warnings.Add($"Recursive method '{method.Identifier.ValueText}' is estimated from its apparent argument reduction; termination and recurrence behavior are not proven.");
        assumptions.Add("Recursive calls are classified syntactically; mutual recursion, memoization, and nonstandard recurrences are not fully modeled.");

        if (HasHalvingReduction(method.Body ?? (SyntaxNode?)method.ExpressionBody ?? method))
            return recursiveCalls > 1 ? Complexity.Linearithmic : Complexity.Logarithmic;
        return recursiveCalls > 1 ? Complexity.ExponentialComplexity : Complexity.Linear;
    }

    private static bool HasHalvingReduction(SyntaxNode node)
    {
        var text = node.ToString();
        return text.Contains("/ 2", StringComparison.Ordinal) || text.Contains(">> 1", StringComparison.Ordinal);
    }

    private static Complexity AnalyzeSpace(SyntaxNode body, HashSet<string> warnings)
    {
        var result = Complexity.Constant;
        foreach (var array in body.DescendantNodes().OfType<ArrayCreationExpressionSyntax>())
        {
            var loopMultiplier = GetEnclosingLoopMultiplier(array, warnings);
            if (loopMultiplier != Complexity.Constant)
                warnings.Add("Array allocations inside loops are assumed to remain live when estimating auxiliary space.");
            result = Complexity.Max(result, GetArraySizeComplexity(array).Multiply(loopMultiplier));
        }
        foreach (var creation in body.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            var loopMultiplier = GetEnclosingLoopMultiplier(creation, warnings);
            var collectionSpace = GetCollectionCreationComplexity(creation);
            if (loopMultiplier != Complexity.Constant && collectionSpace != Complexity.Constant)
                warnings.Add("Collection allocations inside loops are assumed to remain live when estimating auxiliary space.");
            result = Complexity.Max(result, collectionSpace.Multiply(loopMultiplier));
        }

        foreach (var invocation in body.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var name = GetInvokedName(invocation);
            if (name is "ToList" or "ToArray" or "ToDictionary" or "ToLookup" or "GroupBy" or "Distinct" or
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

    private readonly record struct Complexity(int Degree, int LogarithmicPower, bool Exponential = false, bool Unknown = false)
    {
        public bool IsLogarithmic => LogarithmicPower > 0 && Degree == 0;

        public static Complexity Constant => new(0, 0);
        public static Complexity Linear => new(1, 0);
        public static Complexity Logarithmic => new(0, 1);
        public static Complexity Linearithmic => new(1, 1);
        public static Complexity ExponentialComplexity => new(0, 0, Exponential: true);
        public static Complexity UnknownComplexity => new(0, 0, Unknown: true);

        public Complexity Multiply(Complexity other) => new(
            Degree + other.Degree,
            LogarithmicPower + other.LogarithmicPower,
            Exponential || other.Exponential,
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
