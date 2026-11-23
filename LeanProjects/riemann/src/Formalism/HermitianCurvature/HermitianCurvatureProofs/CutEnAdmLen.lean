import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem admissible_length_holds : AdmLen := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a ha
  obtain ⟨w, rfl⟩ := ha
  exact le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2

end Formalism.FourierDecayAlt.P.CutMP.En
