import Mathlib
import Lemmata.GeneralBFactThirdBisForm.Imports

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem swap_mp {ι P β : Type} [Fintype ι] [Fintype P] [MeasurableSpace β] (μ0 : Measure β) [SigmaFinite μ0] :
    MeasurePreserving (fun (x : ι → P → β) (p : P) (v : ι) => x v p)
      (Measure.pi fun _ : ι => Measure.pi fun _ : P => μ0) (Measure.pi fun _ : P => Measure.pi fun _ : ι => μ0) := by
  first | exact Bl.general_b_fact_third_bis_form.goal1 .. | (apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_form.goal1 <;> assumption)

end Formalism.L2.SG.NGCut.SplitEmbedding
