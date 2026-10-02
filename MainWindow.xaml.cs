using System.Windows;

namespace ComplexityAnalyzer;

public partial class MainWindow : Window
{
    private readonly ComplexityAnalyzerService _analyzer = new();

    public MainWindow()
    {
        InitializeComponent();
        CodeInput.Text = """
            public static int FindMax(int[] values)
            {
                int max = int.MinValue;
                for (int i = 0; i < values.Length; i++)
                {
                    if (values[i] > max)
                        max = values[i];
                }
                return max;
            }
            """;
        DisplayResult(_analyzer.Analyze(CodeInput.Text));
    }

    private async void AnalyzeButton_Click(object sender, RoutedEventArgs e)
    {
        var source = CodeInput.Text;
        AnalyzeButton.IsEnabled = false;
        AnalyzeButton.Content = "Analyzing...";

        try
        {
            var result = await Task.Run(() => _analyzer.Analyze(source));
            DisplayResult(result);
        }
        catch (Exception exception)
        {
            TimeComplexityText.Text = "Unavailable";
            SpaceComplexityText.Text = "Unavailable";
            ConfidenceText.Text = "Confidence: —";
            ExplanationText.Text = $"Analysis failed: {exception.Message}";
            AssumptionsList.ItemsSource = Array.Empty<string>();
            WarningsList.ItemsSource = new[] { "The input could not be analyzed." };
            SyntaxErrorsList.ItemsSource = Array.Empty<string>();
        }
        finally
        {
            AnalyzeButton.IsEnabled = true;
            AnalyzeButton.Content = "Analyze code";
        }
    }

    private void ClearButton_Click(object sender, RoutedEventArgs e)
    {
        CodeInput.Clear();
    }

    private void DisplayResult(AnalysisResult result)
    {
        TimeComplexityText.Text = result.TimeComplexity;
        SpaceComplexityText.Text = result.SpaceComplexity;
        ConfidenceText.Text = $"Confidence: {result.ConfidencePercent}%";
        ExplanationText.Text = result.Explanation;
        AssumptionsList.ItemsSource = result.Assumptions;
        WarningsList.ItemsSource = result.Warnings;
        SyntaxErrorsList.ItemsSource = result.SyntaxErrors;
    }
}