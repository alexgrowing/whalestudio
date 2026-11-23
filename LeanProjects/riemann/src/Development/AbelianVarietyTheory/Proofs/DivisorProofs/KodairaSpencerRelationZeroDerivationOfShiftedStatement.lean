import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (lam : Matrix (Fin n) (Fin n) K), lamᵀ = lam → (∀ r, δ₀ (ψ r) = 0) → ∀ (k : ℕ), 1 ≤ k → ∀ (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), ⨆ i, Out.nonzeroLocus (s i) = ⊤ → (∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i)) → (∀ i, (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (valR ξ _ ((s i).f fun _ => j₀)) / valR ξ _ ((s i).f fun _ => j₀)) * δ e (valR ξ _ f))) → KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) lam := by
  first | exact @GlobalTheory.Heat.ZeroKS.ksRel_zero | exact GlobalTheory.Heat.ZeroKS.ksRel_zero | (intros; apply GlobalTheory.Heat.ZeroKS.ksRel_zero <;> assumption)
