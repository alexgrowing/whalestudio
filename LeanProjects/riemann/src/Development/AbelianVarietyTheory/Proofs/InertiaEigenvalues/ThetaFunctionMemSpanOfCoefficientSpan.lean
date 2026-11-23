import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplitStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Decomp

variable {D : D7}

theorem heisO_lin_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f - g) = heisO ψ S T x f - heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_sub]; rfl

theorem heisO_lin_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f + g) = heisO ψ S T x f + heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_add]; rfl

theorem heisO_lin_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) :
    heisO ψ S T x (0 : WO S T → ℂ) = 0 := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]

theorem theta_of_mem_span {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {𝒯 : Set (WO S T → ℂ)}
    (h0 : IsThetaFunO ψ S T 0) (h𝒯 : ∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) {φ : WO S T → ℂ} (hφ : φ ∈ Submodule.span ℂ 𝒯) : IsThetaFunO ψ S T φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h𝒯 x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact theta_add hx hy
  | smul c x _ hx => exact theta_smul c hx

theorem exists_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) (X : Finset (WO S T))
    (hX : ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨
      ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f) :
    ∃ L : WO S T → ((WO S T → ℂ) →ₗ[ℂ] ℂ), (∀ x₁, InvForm ψ S T a (L x₁)) ∧
      ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
        ℓ (heisO ψ S T x f) = ∑ x₁ ∈ X, L x₁ (heisO ψ S T x f) * ℓ (heisO ψ S T x₁ f) := by
  classical
  let K : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {h | ∃ u g, IsHalf (cA D a) u ∧ IsThetaFunO ψ S T g ∧ h = heisO ψ S T u g - g}
  have inv_iff : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, InvForm ψ S T a ℓ ↔ K ≤ LinearMap.ker ℓ := by
    intro ℓ
    constructor
    · intro hℓ
      rw [Submodule.span_le]
      rintro h ⟨u, g, hu, hg, rfl⟩
      simp [LinearMap.mem_ker, map_sub, hℓ u hu g hg]
    · intro hle u hu g hg
      have := hle (Submodule.subset_span ⟨u, g, hu, hg, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
  have inv_comp : ∀ μ : ((WO S T → ℂ) ⧸ K) →ₗ[ℂ] ℂ, InvForm ψ S T a (μ ∘ₗ K.mkQ) := by
    intro μ
    rw [inv_iff]
    intro h hh
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero K).2 hh]
  let Fq : WO S T → (WO S T → ℂ) ⧸ K := fun x => K.mkQ (heisO ψ S T x f)
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) ⧸ K :=
    ∑ x₁ ∈ X, (LinearMap.proj x₁ : (WO S T → ℂ) →ₗ[ℂ] ℂ).smulRight (Fq x₁)
  have hA : ∀ c, A c = ∑ x₁ ∈ X, c x₁ • Fq x₁ := by
    intro c
    simp [A, LinearMap.sum_apply]
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range A).subtype (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.rangeRestrict (LinearMap.range_rangeRestrict A)
  let s := g ∘ₗ p
  have hs : ∀ q ∈ LinearMap.range A, A (s q) = q := by
    intro q hq
    have h1 : p q = ⟨q, hq⟩ := by
      have := LinearMap.congr_fun hp ⟨q, hq⟩
      simpa using this
    have h2 := LinearMap.congr_fun hg (p q)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 : A (g (p q)) = ((A.rangeRestrict (g (p q)) : LinearMap.range A) : (WO S T → ℂ) ⧸ K) := rfl
    simp only [s, LinearMap.comp_apply]
    rw [h3, h2, h1]
  refine ⟨fun x₁ => (LinearMap.proj x₁ ∘ₗ s) ∘ₗ K.mkQ, fun x₁ => inv_comp _, ?_⟩
  intro ℓ hℓ x hx
  have hle := (inv_iff ℓ).1 hℓ
  have hmem : Fq x ∈ LinearMap.range A := by
    rcases hX x hx with h0 | ⟨x₁, hx₁, he⟩
    · have : Fq x = 0 := by
        rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
        intro μ
        exact h0 (μ ∘ₗ K.mkQ) (inv_comp μ)
      rw [this]
      exact Submodule.zero_mem _
    · refine ⟨Pi.single x₁ 1, ?_⟩
      rw [hA, Finset.sum_eq_single x₁]
      · simp [Fq, he]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd hx₁ h
  have key := congrArg (K.liftQ ℓ hle) (hs _ hmem)
  rw [hA, map_sum] at key
  simp only [map_smul, smul_eq_mul] at key
  have hb : ∀ y, K.liftQ ℓ hle (Fq y) = ℓ (heisO ψ S T y f) := fun y => rfl
  simp only [hb] at key
  rw [← key]
  rfl

theorem mem_span_of_coef_mem_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  intro D ψ S T hψ a ha f hf 𝒢 𝒯 h𝒯 h𝒢 hcoef
  obtain ⟨-, -, X, hXh, hX⟩ := GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) a ha f hf
  obtain ⟨L, hLinv, hL⟩ := exists_decomp ψ S T a f X hX
  have hspan : ∀ Ψ ∈ Submodule.span ℂ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ →
      ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f) := by
    intro Ψ hΨ x₁ hx₁
    induction hΨ using Submodule.span_induction with
    | mem Ψ hΨ => exact h𝒢 Ψ hΨ x₁ hx₁
    | zero => exact ⟨0, Submodule.zero_mem _, fun ℓ _ x _ => by simp [heisO_lin_zero]⟩
    | add Ψ₁ Ψ₂ _ _ h1 h2 =>
      obtain ⟨φ₁, m1, e1⟩ := h1
      obtain ⟨φ₂, m2, e2⟩ := h2
      refine ⟨φ₁ + φ₂, add_mem m1 m2, fun ℓ hℓ x hx => ?_⟩
      rw [heisO_lin_add, map_add, e1 ℓ hℓ x hx, e2 ℓ hℓ x hx, Pi.add_apply, add_mul]
    | smul c Ψ _ h =>
      obtain ⟨φ, m, e⟩ := h
      refine ⟨c • φ, Submodule.smul_mem _ c m, fun ℓ hℓ x hx => ?_⟩
      rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, e ℓ hℓ x hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hφ : ∀ x₁ ∈ X, ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x φ) = coef ψ S T a (L x₁) f x * ℓ (heisO ψ S T x₁ f) :=
    fun x₁ hx₁ => hspan _ (hcoef _ (hLinv x₁)) x₁ (hXh x₁ hx₁)
  choose! φ hφm hφe using hφ
  have hsum : (∑ x₁ ∈ X, φ x₁) ∈ Submodule.span ℂ 𝒯 := Submodule.sum_mem _ hφm
  have h0 : IsThetaFunO ψ S T 0 := by simpa using theta_sub hf hf
  have hzero := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha (f - ∑ x₁ ∈ X, φ x₁)
    (theta_sub hf (theta_of_mem_span h0 h𝒯 hsum)) (by
      intro ℓ hℓ x hx
      rw [heisO_lin_sub, GlobalTheory.SplitScalar.heisO_sum, map_sub, map_sum, hL ℓ hℓ x hx, sub_eq_zero]
      refine Finset.sum_congr rfl fun x₁ hx₁ => ?_
      rw [hφe x₁ hx₁ ℓ hℓ x hx, coef, if_pos hx])
  rw [sub_eq_zero] at hzero
  exact hzero ▸ hsum

end GlobalTheory.DownLift.SplitCoef.Decomp
