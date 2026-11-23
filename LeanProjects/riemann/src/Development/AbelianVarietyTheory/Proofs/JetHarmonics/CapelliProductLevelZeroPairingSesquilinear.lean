import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniformStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliFoldAddSmul

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_foldCapelli_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA a X X' Z Z' hX hX' hXc hX'c hZ hZ'
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  obtain ⟨c, hc⟩ := hXc
  obtain ⟨c', hc'⟩ := hX'c
  have h1 : B.InCC A 5 _ := ⟨_, hK A c X hX hc⟩
  have h2 : B.InCC A 5 _ := ⟨_, hK A c' X' hX' hc'⟩
  refine ⟨?_, (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA hZ hZ' h1 a).2⟩
  rw [← (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA h1 h2 hZ a).1]
  exact Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr Bs (fun g hg => GlobalTheory.capelliFold_add_smul k r Wp Wq s w a X X' hX hX' g hg)

end GlobalTheory
