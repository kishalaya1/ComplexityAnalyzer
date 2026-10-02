namespace ComplexityAnalyzer;

public sealed record AnalysisResult(
    string TimeComplexity,
    string SpaceComplexity,
    string Explanation,
    IReadOnlyList<string> Assumptions,
    IReadOnlyList<string> Warnings,
    int ConfidencePercent,
    IReadOnlyList<string> SyntaxErrors);
