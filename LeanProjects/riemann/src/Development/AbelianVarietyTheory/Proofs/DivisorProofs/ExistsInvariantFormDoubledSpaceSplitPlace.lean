import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCmStatement
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblSplitForm

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_ext_form (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) (l0 : M →ₗ[ℂ] ℂ) (gen : Set M)
    (hinv : ∀ u ∈ Y, ∀ p ∈ gen, l0 (ρ u p) = l0 p) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ∀ p ∈ gen, ℓ p = l0 p := by
  classical
  let P : Submodule ℂ M := Submodule.span ℂ gen
  let K : Submodule ℂ M := Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}
  have hl0P : ∀ u ∈ Y, ∀ p ∈ P, l0 (ρ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf => exact hinv u hu f hf
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, -⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero hadd h0 hsm hmK
    have h1 : l0 (∑ j ∈ s, ρ (y j) m) = (s.card : ℂ) * l0 m := by
      rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc
  let fP : M →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : M →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : M) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : M) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu g hg => ?_, fun p hp => ?_⟩
  · have hk : ρ u g - g ∈ K := Submodule.subset_span ⟨u, hu, g, hg, rfl⟩
    have hz : ρ u g - g ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (ρ u g - g) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp' : p ∈ P := Submodule.subset_span hp
    have hz : p ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp'
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp'⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 p + 0 = _
    rw [add_zero]

end Abstract

def conjForm {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := conj (ℓ (fun y => conj (g y)))
  map_add' a b := by
    have : (fun y => conj ((a + b) y)) = (fun y => conj (a y)) + fun y => conj (b y) := by
      funext y; simp
    rw [this, map_add, map_add]
  map_smul' c a := by
    have : (fun y => conj ((c • a) y)) = conj c • fun y => conj (a y) := by
      funext y; simp
    rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]

theorem conjForm_mul {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (b : X → ℂ) :
    conjForm ℓ (fun y => c * conj (b y)) = c * conj (ℓ b) := by
  have : (fun y => conj (c * conj (b y))) = conj c • b := by
    funext y; simp
  show conj (ℓ (fun y => conj (c * conj (b y)))) = _
  rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def joinR (x₁ x₂ : WOF F E nS nT) : WOF F E nS (nT + nT) := (Matrix.fromRows x₁ x₂).submatrix finSumFinEquiv.symm id

theorem topR_joinR (x₁ x₂ : WOF F E nS nT) : topR (joinR x₁ x₂) = x₁ := by
  ext i j
  simp [joinR, topR, Matrix.submatrix_apply]

theorem botR_joinR (x₁ x₂ : WOF F E nS nT) : botR (joinR x₁ x₂) = x₂ := by
  ext i j
  show Matrix.fromRows x₁ x₂ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j = x₂ i j
  rw [Equiv.symm_apply_apply]; rfl

def dblForm (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ :=
  ℓ ∘ₗ LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y))

theorem dblForm_deltaT (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) (a b : WOF F E nS nT → ℂ) :
    dblForm ℓ (deltaT a b) = ℓ a * conj (ℓ b) := by
  have h : (LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y)))
      (deltaT a b) = conj (ℓ b) • a := by
    funext x₁
    have e : (LinearMap.funLeft ℂ ℂ (fun y : WOF F E nS nT => joinR x₁ (-y))) (deltaT a b) =
        fun y => a x₁ * conj (b y) := by
      funext y
      simp [LinearMap.funLeft_apply, deltaT_apply, topR_joinR, botR_joinR]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, e, conjForm_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dblForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DblSplitForm

namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

theorem exists_invForm_dbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    GlobalTheory.T.exists_nonzero_thetaFun_oriented_model_cm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := GlobalTheory.T.exists_splitPlace_conjHeisenberg_invariantForm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := GlobalTheory.DblHeis.heisOF_dblG_deltaT F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)

end GlobalTheory.DblSplitForm
