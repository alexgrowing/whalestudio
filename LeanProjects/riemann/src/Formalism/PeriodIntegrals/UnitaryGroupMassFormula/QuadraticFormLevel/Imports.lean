import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.Q.RttLevelZero

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem main : RTTLevelFromUpper := by
  intro hUp hLT hGI hFF _hTL k r i
  refine Fin.cases ?_ (fun l => hUp k r l) i
  intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
  obtain ⟨π₁, π₁', D₁, f, hz1, hz1', hD1, hf, hι⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
  have hgU : g ∈ UH (Hpk k r) := hg.1.1
  have hιg : ιLev k 1 r g ∈ Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
    refine ⟨?_, (hι g hgU).1.mpr hg.2⟩
    rw [hGI k 1 r]
    exact ⟨g, hgU, rfl⟩
  have h1 : RTTAt k (1 + r) ⟨1, by omega⟩ := hUp k (1 + r) ⟨0, by omega⟩
  have key := h1 Wp Wq (liftVec k 1 r z) (liftVec k 1 r z') π₁ π₁' D₁ hz1 hz1' hD1 f hf
    (ιLev k 1 r g) hιg u v a b c d
  have step : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
      tL k (1 + r) (liftVec k 1 r z) (liftVec k 1 r z') ⟨1, by omega⟩ Y p q
        (tL k (1 + r) (liftVec k 1 r z) (liftVec k 1 r z') ⟨1, by omega⟩ Y' p' q' f) (ιLev k 1 r g) =
      tL k r z z' 0 Y p q (tL k r z z' 0 Y' p' q' J) g := by
    intro Y Y' p q p' q'
    rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hgU]
    refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := (0 : Fin (r + 1))) hD.1 z z' Y p q).loc
      _ _ ?_ g hg
    intro x hx
    rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
    exact (Formalism.FourierDecayAlt.P.Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := (0 : Fin (r + 1))) hD.1 z z' Y' p' q').loc
      _ _ (fun y hy => (hι y hy.1.1).2) x hx
  simp only [step] at key
  exact key

end Formalism.FourierDecayAlt.Q.RttLevelZero
