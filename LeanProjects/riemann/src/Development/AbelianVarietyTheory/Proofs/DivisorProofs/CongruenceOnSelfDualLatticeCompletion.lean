import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatHatCong

theorem cong_zero {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ) :
    t • (K *ᵥ 0 - 0) = M • (0 : Fin n → R) := by
  rw [Matrix.mulVec_zero, sub_zero, smul_zero, smul_zero]

theorem cong_add {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u w y y' : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) (e' : t • (K *ᵥ w - w) = M • y') :
    t • (K *ᵥ (u + w) - (u + w)) = M • (y + y') := by
  rw [Matrix.mulVec_add, add_sub_add_comm, smul_add, e, e', smul_add]

theorem cong_neg {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (-u) - (-u)) = M • (-y) := by
  rw [Matrix.mulVec_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, smul_neg, e, smul_neg]

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t c : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (c • u) - c • u) = M • (c • y) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, e, smul_comm]

theorem cong_on_hat : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  intro D V β Λ hβ K t M h z hz
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl] at h hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    obtain ⟨y, hy, e⟩ := h x hx
    have hm : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hy' := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ hm y hy
    have hc : (Algebra.TensorProduct.comm D.host.F _ D.host.E).symm ((1 : D.host.E) ⊗ₜ[D.host.F] a) =
        a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc] at hy'
    have hv : (fun i => a ⊗ₜ[D.host.F] x i) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • finVec V x := by
      funext i
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    refine ⟨_, hy', ?_⟩
    rw [hv]
    exact cong_smul e
  | zero =>
    exact ⟨0, AddSubgroup.zero_mem _, cong_zero K t M⟩
  | add u w _ _ hu hw =>
    obtain ⟨y, hy, e⟩ := hu
    obtain ⟨y', hy', e'⟩ := hw
    exact ⟨y + y', add_mem hy hy', cong_add e e'⟩
  | neg u _ hu =>
    obtain ⟨y, hy, e⟩ := hu
    exact ⟨-y, neg_mem hy, cong_neg e⟩

end GlobalTheory.LatHatCong
