import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_trivial_on_projective_cover : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (J : Type) (U : J → X.Opens) (n : J → ℕ) (G : ∀ j j', Matrix (Fin (n j)) (Fin (n j')) Γ(X, U j ⊓ U j')), IsProjOver s → (∀ x : X, ∃ j, x ∈ U j) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j, ⊤ ≤ w ⁻¹ᵁ U j → (G j j).map (valF w _) = 1) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j j' j'', ⊤ ≤ w ⁻¹ᵁ U j → ⊤ ≤ w ⁻¹ᵁ U j' → ⊤ ≤ w ⁻¹ᵁ U j'' → (G j j').map (valF w _) * (G j' j'').map (valF w _) = (G j j'').map (valF w _)) → ∃ (L : FinLB X) (M : ℕ) (σ : Fin L.n → J) (A : ∀ i, Matrix (Fin (M + 1)) (Fin (n (σ i))) Γ(X, L.U i)) (B : ∀ i, Matrix (Fin (n (σ i))) (Fin (M + 1)) Γ(X, L.U i)), (∀ i, IsAffineOpen (L.U i)) ∧ (∀ i, L.U i ≤ U (σ i)) ∧ (∀ i, B i * A i = 1) ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i', ⊤ ≤ w ⁻¹ᵁ L.U i → ⊤ ≤ w ⁻¹ᵁ L.U i' → (A i).map (valF w _) = valF w _ (L.g i i').val • ((A i').map (valF w _) * (G (σ i') (σ i)).map (valF w _)) := by
  first | exact @GlobalTheory.TwistEmb.exists_twist_embedding | exact GlobalTheory.TwistEmb.exists_twist_embedding | (intros; apply GlobalTheory.TwistEmb.exists_twist_embedding <;> assumption)
