import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualOneFormsInvariantFieldsAffineOpenStatement
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
namespace GlobalTheory.Heat.SymReg

theorem sum_sum_bilin_regroup {I₁ I₂ J₁ J₂ R : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂] [CommRing R]
    (x : I₁ → R) (y : I₂ → R) (L : J₁ → J₂ → R) (u : J₁ → I₁ → R) (w : J₂ → I₂ → R) :
    ∑ i, ∑ j, x i * y j * ∑ a, ∑ e, L a e * u a i * w e j
      = ∑ a, ∑ e, L a e * (∑ i, x i * u a i) * (∑ j, y j * w e j) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ a, ∑ e, x i * y j * (L a e * u a i * w e j)
      = ∑ i, ∑ a, ∑ e, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ i, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ j, ∑ i, L a e * (x i * u a i) * (y j * w e j) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (Λ : Matrix (Fin n) (Fin n) F) (W : P₀.A.left.Opens), IsAffineOpen W → ⊤ ≤ ξ ⁻¹ᵁ W → (∀ f f' : Γ(P₀.A.left, W), ∃ h : Γ(P₀.A.left, W), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) → ∀ a e, ∃ h : Γ(P₀.A.left, W), valR ξ W h = Λ a e := by
  intro K _ _ P₀ n v dd hinv F _ ψ ξ _ _ δ hδ Λ W hW hξW hΛ a e
  let φ : Γ(P₀.A.left, W) →+* F :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (ξ.appLE W ⊤ hξW).hom
  have hφ : ∀ f, valR ξ W f = φ f := fun f => by
    unfold valR; rw [dif_pos hξW]; rfl
  have hδ' : ∀ b x, φ (dd b W x) = δ b (φ x) := fun b x => by
    rw [← hφ, ← hφ]; exact hδ b W x hξW
  obtain ⟨N, g, f, hgf⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW a
  obtain ⟨N', g', f', hgf'⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW e
  choose h hh using fun (i : Fin N) (j : Fin N') => hΛ (f i) (f' j)
  have hh' : ∀ i j, φ (h i j) = ∑ a', ∑ e', Λ a' e' * δ a' (φ (f i)) * δ e' (φ (f' j)) := by
    intro i j; rw [← hφ, hh]; simp only [hφ]
  have key : ∀ b, ∑ i, φ (g i) * δ b (φ (f i)) = if a = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf b)
    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  have key' : ∀ b, ∑ j, φ (g' j) * δ b (φ (f' j)) = if e = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf' b)
    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  refine ⟨∑ i, ∑ j, g i * g' j * h i j, ?_⟩
  rw [hφ]
  simp only [map_sum, map_mul, hh']
  rw [sum_sum_bilin_regroup (fun i => φ (g i)) (fun j => φ (g' j)) Λ (fun a' i => δ a' (φ (f i)))
    (fun e' j => δ e' (φ (f' j)))]
  simp only [key, key', mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.Heat.SymReg
