import Mathlib
import GroundTheory.PAdicHodge.AxLemma

open Filter Topology

namespace GlobalTheory

theorem exists_baseChange_extension_of_flat {A K E M : Type*} [CommRing A] [Field K] [Algebra A K]
    [Module.Flat A K] [AddCommGroup E] [Module K E] [AddCommGroup M] [Module A M]
    (B : Submodule A M) (Θ : B → E)
    (h : ∀ (a a' : A) (b b' : B),
      Θ (a • b + a' • b') = algebraMap A K a • Θ b + algebraMap A K a' • Θ b') :
    ∃ L : TensorProduct A K M →ₗ[K] E, ∀ b : B, L (1 ⊗ₜ[A] (b : M)) = Θ b := by
  letI : Module A E := Module.compHom E (algebraMap A K)
  have hs : ∀ (a : A) (e : E), a • e = algebraMap A K a • e := fun _ _ => rfl
  haveI : IsScalarTower A K E := ⟨fun a k e => by rw [hs, Algebra.smul_def, mul_smul]⟩
  let Θ' : B →ₗ[A] E :=
    { toFun := Θ
      map_add' := fun b b' => by simpa using h 1 1 b b'
      map_smul' := fun a b => by
        have := h a 0 b b
        rwa [zero_smul, add_zero, map_zero, zero_smul, add_zero] at this }
  have hinj : Function.Injective (B.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange K)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(Θ'.liftBaseChange K).comp r, fun b => ?_⟩
  have h1 : r (1 ⊗ₜ[A] (b : M)) = 1 ⊗ₜ[A] b := by
    simpa using LinearMap.congr_fun hr (1 ⊗ₜ[A] b)
  rw [LinearMap.comp_apply, h1, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem tendsto_appr_padicComplex (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) :
    Tendsto (fun n => (((a.appr n : ℕ) : PadicAlgCl l) : ℂ_[l])) atTop
      (𝓝 ((algebraMap ℤ_[l] (PadicAlgCl l) a : PadicAlgCl l) : ℂ_[l])) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq)
  have hn : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ = ‖z‖ := fun z =>
    PadicAlgCl.norm_extends l (z : ℚ_[l])
  rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hn, norm_sub_rev]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  rw [← ht, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) t.norm_le_one

theorem exists_linear_limit_of_compatible_family :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
      (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
    (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
    (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y →
      ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
    (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
      R n (a • b + a' • b')
        (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
    ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x,
      R n b x → ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  intro l _ M _ _ B R C h1 h2 h3
  simp only [norm_pow] at h2 ⊢
  set q : ℝ := ‖((l : ℕ) : PadicAlgCl l)‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  choose! x hx using h1
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans
      (h2 0 0 B.zero_mem _ _ (hx 1 0 B.zero_mem) (hx 0 0 B.zero_mem))
    simpa using this
  have hmono : ∀ {n m : ℕ}, n ≤ m → C * q ^ m ≤ C * q ^ n := fun h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le h) hC
  have htail : ∀ n, ∀ b ∈ B, ∀ y, R n b y → ∀ m, n + 1 ≤ m → ‖x m b - y‖ ≤ C * q ^ n := by
    intro n b hb y hy m hm
    induction m, hm using Nat.le_induction with
    | base => exact h2 n b hb _ _ (hx _ b hb) hy
    | succ m hm ih =>
      have e : x (m + 1) b - y = (x (m + 1) b - x m b) + (x m b - y) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (h2 m b hb _ _ (hx _ b hb) (hx _ b hb)).trans (hmono (by omega))
  have hlim : ∀ b : B, ∃ z : ℂ_[l], Tendsto (fun n => ((x n b : PadicAlgCl l) : ℂ_[l])) atTop (𝓝 z) := by
    intro b
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 fun n => ?_)
    rw [dist_eq_norm, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact h2 n b b.2 _ _ (hx _ _ b.2) (hx _ _ b.2)
  choose Θ hΘ using hlim
  have hbound : ∀ n (b : B) (y : PadicAlgCl l), R n b y → ‖(y : ℂ_[l]) - Θ b‖ ≤ C * q ^ n := by
    intro n b y hy
    refine le_of_tendsto ((tendsto_const_nhds (x := (y : ℂ_[l]))).sub (hΘ b)).norm
      (eventually_atTop.2 ⟨n + 1, fun m hm => ?_⟩)
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact htail n b b.2 y hy m hm
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := Module.Flat.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  obtain ⟨L, hL⟩ := exists_baseChange_extension_of_flat (K := PadicAlgCl l) B Θ (by
    intro a a' b b'
    have hA := ((tendsto_appr_padicComplex l a).mul (hΘ b)).add
      ((tendsto_appr_padicComplex l a').mul (hΘ b'))
    rw [Algebra.smul_def, Algebra.smul_def]
    refine tendsto_nhds_unique ?_ hA
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have := hbound n (a • b + a' • b') _
      (h3 n b b.2 b' b'.2 a a' _ _ (hx n _ b.2) (hx n _ b'.2))
    rwa [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
      UniformSpace.Completion.coe_mul] at this)
  refine ⟨L, fun n b hb y hy => ?_⟩
  rw [show L (1 ⊗ₜ[ℤ_[l]] b) = Θ ⟨b, hb⟩ from hL ⟨b, hb⟩]
  exact hbound n ⟨b, hb⟩ y hy

end GlobalTheory
