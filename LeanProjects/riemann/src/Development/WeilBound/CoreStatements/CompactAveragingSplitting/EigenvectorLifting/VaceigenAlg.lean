import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam

noncomputable section

namespace PositivityTheory.ThK.Vac

open scoped nonZeroDivisors Matrix

theorem dual_family (R K : Type) {V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] (L : Submodule R V) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (m : ℕ) (g : Fin m → V) (f : Fin m → V →ₗ[K] K), (∀ i, g i ∈ L) ∧ (∀ i, ∀ x ∈ L, ∃ r : R, algebraMap R K r = f i x) ∧
      ∀ x, x = ∑ i, f i x • g i := by
  have : Module.Finite R L := Module.Finite.iff_fg.2 hfg
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R K V
  have : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  have : IsLocalizedModule R⁰ L.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
    · rw [Module.End.isUnit_iff]
      have hs : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have : ⇑(algebraMap R (Module.End R V) s) = fun x => algebraMap R K s • x := by
        ext x; simp
      rw [this]
      exact (MulAction.toPerm (Units.mk0 _ hs)).bijective
    · obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span R⁰ K (L : Set V) y (hsp ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  let f : Fin m → V →ₗ[K] K := fun i =>
    IsLocalizedModule.mapExtendScalars R⁰ L.subtype (Algebra.linearMap R K) K ((LinearMap.proj i : (Fin m → R) →ₗ[R] R) ∘ₗ s)
  have hf : ∀ i (x : L), f i x = algebraMap R K (s x i) := fun i x =>
    IsLocalizedModule.map_apply R⁰ L.subtype (Algebra.linearMap R K) ((LinearMap.proj i : (Fin m → R) →ₗ[R] R) ∘ₗ s) x
  refine ⟨m, fun i => p (Pi.single i 1), f, fun i => (p _).2, fun i x hx => ⟨_, (hf i ⟨x, hx⟩).symm⟩, fun x => ?_⟩
  have hx : x ∈ Submodule.span K (L : Set V) := hsp ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have h1 : p (s ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hps _
    rw [pi_eq_sum_univ' (s ⟨x, hx⟩), map_sum] at h1
    have h2 := congrArg Subtype.val h1
    simp only [map_smul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h2
    conv_lhs => rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [hf i ⟨x, hx⟩, algebraMap_smul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, ← hx, ← hy]
  | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]

open GlobalTheory.CompanionTheory.FinHeis in

theorem line_of_eigen {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M) (Γ : Set X) (χ : X → ℂ)
    (hΓ : ∀ x, (∀ γ ∈ Γ, S.c γ x ^ 2 = 1) → x ∈ Γ) {φ φ' : M} (h0 : φ ≠ 0) (hc : Cyclic S φ)
    (hφ : ∀ γ ∈ Γ, S.rho γ φ = χ γ • φ) (hφ' : ∀ γ ∈ Γ, S.rho γ φ' = χ γ • φ') : ∃ a : ℂ, φ' = a • φ := by
  have hne : S.B φ φ ≠ 0 := fun h => by simpa [h] using S.B_pos φ h0
  have hχ : ∀ γ ∈ Γ, (starRingEnd ℂ) (χ γ) * χ γ = 1 := fun γ hγ => by
    have h := S.B_rho γ φ φ
    rw [hφ γ hγ] at h
    simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h
    refine mul_right_cancel₀ hne ?_
    linear_combination h
  have key : ∀ η : M, (∀ γ ∈ Γ, S.rho γ η = χ γ • η) → S.B η φ = 0 → η = 0 := by
    intro η hη h1
    have hall : ∀ x, S.B η (S.rho x φ) = 0 := by
      intro x
      by_cases hx : x ∈ Γ
      · rw [hφ x hx, map_smul, h1, smul_zero]
      · by_contra hn
        refine hx (hΓ x fun γ hγ => mul_right_cancel₀ hn ?_)
        have h2 := S.B_rho γ η (S.rho x φ)
        have h3 : S.rho γ (S.rho x φ) = S.c γ x ^ 2 • S.rho x (S.rho γ φ) := by
          rw [S.rho_rho, S.rho_rho, smul_smul, add_comm x γ, pow_two, mul_assoc, S.c_mul_c_swap, mul_one]
        rw [h3, hφ γ hγ, hη γ hγ] at h2
        simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h2
        linear_combination h2 - S.c γ x ^ 2 * S.B η (S.rho x φ) * hχ γ hγ
    have hle : Submodule.span ℂ (Set.range fun x => S.rho x φ) ≤ LinearMap.ker (S.B η) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hall x
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x φ) = ⊤ from hc] at hle
    have h4 : S.B η η = 0 := hle Submodule.mem_top
    by_contra hn
    simpa [h4] using S.B_pos η hn
  refine ⟨S.B φ φ' / S.B φ φ, sub_eq_zero.1 (key _ (fun γ hγ => ?_) ?_)⟩
  · rw [map_sub, map_smul, hφ γ hγ, hφ' γ hγ, smul_sub, smul_comm]
  · rw [← S.B_conj, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne, sub_self, map_zero]

theorem norm_addChar {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (O : Subring K)
    (hO : IsCompact (O : Set K)) (ψ : AddChar K ℂ) (hψ : Continuous ψ) (x : K) : ‖ψ x‖ = 1 := by
  have h : ∀ x : K, ‖ψ x‖ ≤ 1 := fun x => by
    obtain ⟨C, hC⟩ := hO.exists_bound_of_continuousOn (f := fun y => ψ (y * x)) (by fun_prop)
    by_contra hn
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 hn)
    have := hC k (natCast_mem O k)
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
    exact absurd hk (not_lt.2 this)
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [h x, h (-x), norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

end PositivityTheory.ThK.Vac
