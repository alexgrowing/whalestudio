import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_restriction : ∀ {X W : Scheme.{0}} (jB : W ⟶ X) {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ} {g : ℕ}
    (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) {U V V' : X.Opens} (hV : V ≤ U) (hV' : V' ≤ V)
    (ℓ : Fin g → Γ(L, U)) (hℓ : VB.IsFrame ℓ) (f : ∀ a, Fin (r a) → Γ(E a, V)), (∀ a, VB.IsFrame (f a)) →
    ∀ (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (hf' : ∀ a, VB.IsFrame (f' a))
      (A : Matrix (Fin g) (Σ a, Fin (r a)) Γ(W, jB ⁻¹ᵁ V)),
    (∀ a b i, jB.app V ((hℓ.basis hV).repr ((T a).app V (f a i)) b) =
      ∑ j, A b ⟨a, j⟩ * jB.app V (((hf' a).basis le_rfl).repr ((u a).app V (f a i)) j)) →
    Function.Injective (jB.app V') →
    ∀ (C : Matrix (Fin g) (Σ a, Fin (r a)) Γ(X, V')) (C' : Matrix (Σ a, Fin (r a)) (Fin g) Γ(X, V'))
      (Q : Matrix (Σ a, Fin (r a)) (Σ a, Fin (r a)) Γ(W, jB ⁻¹ᵁ V')), C * C' = 1 → C' * C = 1 →
      BlockUni (fun s : Σ a, Fin (r a) => o s.1) Q → C.map (jB.app V') = A.map (resG W (jB.preimage_mono hV')) * Q →
    LocAdapted r o T u V' := by
  first | exact @GlobalTheory.LieFilt.locAdapted_of_matrix | exact GlobalTheory.LieFilt.locAdapted_of_matrix | (intros; apply GlobalTheory.LieFilt.locAdapted_of_matrix <;> assumption)
