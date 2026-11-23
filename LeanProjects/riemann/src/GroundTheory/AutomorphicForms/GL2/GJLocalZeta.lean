import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLaurentIdeal
import GroundTheory.AutomorphicForms.GL2.GJZetaCore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Polynomial

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

section RatFunc

theorem exists_eval_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → Q.eval x ≠ 0 := by
  classical
  set S : Finset ℝ := ((Q.roots.toFinset).filter (· ≠ 0)).image (‖·‖)
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_, fun x hx hxε hQx => ?_⟩
    · obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.1 (S.min'_mem hS)
      rw [← hyeq]
      exact norm_pos_iff.2 (Finset.mem_filter.1 hy).2
    · have hmem : ‖x‖ ∈ S := Finset.mem_image.2 ⟨x, Finset.mem_filter.2
        ⟨Multiset.mem_toFinset.2 ((mem_roots hQ).2 hQx), hx⟩, rfl⟩
      exact absurd (S.min'_le _ hmem) (not_le.2 hxε)
  · refine ⟨1, one_pos, fun x hx _ hQx => hS ⟨‖x‖, Finset.mem_image.2 ⟨x, Finset.mem_filter.2
      ⟨Multiset.mem_toFinset.2 ((mem_roots hQ).2 hQx), hx⟩, rfl⟩⟩⟩

theorem exists_eval_denom_ne_zero (R : RatFunc ℂ) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R.denom.eval x ≠ 0 :=
  exists_eval_ne_zero R.denom_ne_zero

theorem exists_eval_mul (R₁ R₂ : RatFunc ℂ) :
    ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
      (R₁ * R₂).eval (RingHom.id ℂ) x = R₁.eval (RingHom.id ℂ) x * R₂.eval (RingHom.id ℂ) x := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_eval_denom_ne_zero R₁
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_eval_denom_ne_zero R₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx hxε => ?_⟩
  exact RatFunc.eval_mul (f := RingHom.id ℂ) (a := x) (h₁ x hx (hxε.trans_le (min_le_left _ _)))
    (h₂ x hx (hxε.trans_le (min_le_right _ _)))

end RatFunc

theorem qs_add (a b : ℂ) : qs F (a + b) = qs F a * qs F b := by
  rw [qs, qs, qs, neg_add, Complex.cpow_add _ _
    (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero)]

theorem exists_qs_of_small (S : ℝ) : ∃ ε > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε →
    ∃ s : ℂ, S < s.re ∧ qs F s = x := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by
    exact_mod_cast LocalField.one_lt_residueCard (K := F)
  refine ⟨(LocalField.residueCard F : ℝ) ^ (-S), Real.rpow_pos_of_pos (by linarith) _,
    fun x hx hxε => ?_⟩
  obtain ⟨s, hs, hre⟩ := exists_qs_eq (F := F) hx
  refine ⟨s, ?_, hs⟩
  rw [hre]
  have h1 : Real.logb (LocalField.residueCard F) ‖x‖ <
      Real.logb (LocalField.residueCard F) ((LocalField.residueCard F : ℝ) ^ (-S)) :=
    Real.logb_lt_logb hq (norm_pos_iff.2 hx) hxε
  rw [Real.logb_rpow (by linarith) hq.ne'] at h1
  linarith

def zetaIntegral (μ : Measure (GL (Fin n) F)) (Φ : Matrix (Fin n) (Fin n) F → ℂ)
    (f : GL (Fin n) F → ℂ) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * f g * detPow g (s + ((n : ℂ) - 1) / 2) ∂μ

def zetaSet (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) :
    Set (RatFunc ℂ) :=
  {R | ∃ (Φ : Matrix (Fin n) (Fin n) F → ℂ) (v : V) (ℓ : Module.Dual ℂ V),
    IsSchwartzBruhat Φ ∧ ℓ ∈ smoothVectors (Representation.dual π) ∧
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        zetaIntegral μ Φ (matrixCoeff π v ℓ) s = R.eval (RingHom.id ℂ) (qs F s)}

def zetaIdeal (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) :
    Submodule ℂ (RatFunc ℂ) :=
  Submodule.span ℂ (zetaSet π μ)

variable {π : Representation ℂ (GL (Fin n) F) V}

theorem re_shift (s : ℂ) : (s + ((n : ℂ) - 1) / 2).re = s.re + ((n : ℝ) - 1) / 2 := by
  simp [Complex.add_re, Complex.sub_re]

theorem exists_zeta_rat [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ (∀ s : ℂ, s₀ < s.re → D.eval (qs F s) ≠ 0) ∧
      ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
        ℓ ∈ smoothVectors (Representation.dual π) →
        (∀ s : ℂ, s₀ < s.re → Integrable (fun g : GL (Fin n) F =>
          Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
            detPow g (s + ((n : ℂ) - 1) / 2)) μ) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          zetaIntegral μ Φ (matrixCoeff π v ℓ) s =
            (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D)).eval
              (RingHom.id ℂ) (qs F s) := by
  obtain ⟨s₀, D, hD0, hcore⟩ := exists_zeta_core hπ μ
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  set D' : ℂ[X] := D.comp (C c * X) with hD'def
  have hD'0 : D'.eval 0 = 1 := by simp [D', hD0]
  have hD'ne : D' ≠ 0 := fun h => by rw [h, eval_zero] at hD'0; exact zero_ne_one hD'0
  obtain ⟨ε, hε, hεD⟩ := exists_eval_ne_zero hD'ne
  obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
  have hre : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re →
      s₀ < (s + ((n : ℂ) - 1) / 2).re := fun s hs => by
    have := (le_max_left _ _).trans_lt hs
    rw [re_shift]
    linarith
  have hDs : ∀ s : ℂ, max (s₀ - ((n : ℝ) - 1) / 2) s₁ < s.re → D'.eval (qs F s) ≠ 0 :=
    fun s hs => hεD _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs))
  refine ⟨max (s₀ - ((n : ℝ) - 1) / 2) s₁, D', hD'0, hDs, fun Φ hΦ v ℓ hℓ => ?_⟩
  obtain ⟨hint, N, P, hP⟩ := hcore Φ hΦ v ℓ hℓ
  refine ⟨fun s hs => hint _ (hre s hs), N, C (c ^ N)⁻¹ * P.comp (C c * X), fun s hs => ?_⟩
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hDx := hDs s hs
  have hQ : (X ^ N * D').eval (qs F s) ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X]
    exact mul_ne_zero (pow_ne_zero _ hx) hDx
  rw [eval_div_algebraMap _ _ hQ]
  have h1 := hP _ (hre s hs)
  rw [qs_add, ← hcdef] at h1
  have hDx' : D.eval (qs F s * c) ≠ 0 := by
    rw [mul_comm]
    rw [hD'def, eval_comp, eval_mul, eval_C, eval_X] at hDx
    exact hDx
  have h2 := eq_div_of_mul_eq hDx' ((mul_comm _ _).trans h1)
  rw [zetaIntegral, h2]
  simp only [D', eval_mul, eval_comp, eval_C, eval_X, eval_pow]
  rw [mul_comm c (qs F s), mul_pow]
  field_simp

theorem exists_integrable_zetaIntegral [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
      ℓ ∈ smoothVectors (Representation.dual π) → ∀ s : ℂ, s₀ < s.re →
        Integrable (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
          detPow g (s + ((n : ℂ) - 1) / 2)) μ := by
  obtain ⟨s₀, _, _, _, h⟩ := exists_zeta_rat hπ μ
  exact ⟨s₀, fun Φ hΦ v ℓ hℓ => (h Φ hΦ v ℓ hℓ).1⟩

theorem exists_ratFunc_zetaIntegral [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
      ℓ ∈ smoothVectors (Representation.dual π) → ∃ R : RatFunc ℂ, ∀ s : ℂ, s₀ < s.re →
        zetaIntegral μ Φ (matrixCoeff π v ℓ) s = R.eval (RingHom.id ℂ) (qs F s) := by
  obtain ⟨s₀, _, _, _, h⟩ := exists_zeta_rat hπ μ
  refine ⟨s₀, fun Φ hΦ v ℓ hℓ => ?_⟩
  obtain ⟨-, N, P, hP⟩ := h Φ hΦ v ℓ hℓ
  exact ⟨_, hP⟩

theorem zetaIntegral_translate (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a : GL (Fin n) F)
    (Φ : Matrix (Fin n) (Fin n) F → ℂ) (v : V) (ℓ : Module.Dual ℂ V) (s : ℂ) :
    zetaIntegral μ (fun Y => Φ (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Y))
      (matrixCoeff π v (Representation.dual π a ℓ)) s =
      detPow a (s + ((n : ℂ) - 1) / 2) * zetaIntegral μ Φ (matrixCoeff π v ℓ) s := by
  rw [zetaIntegral, zetaIntegral, ← integral_const_mul,
    ← integral_mul_left_eq_self (μ := μ) _ a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [matrixCoeff, dual_apply_apply, ← Module.End.mul_apply, ← map_mul, ← mul_assoc,
    ← Units.val_mul, inv_mul_cancel, one_mul, detPow_mul]
  ring

theorem mem_zetaSet_of_translate (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {R R' : RatFunc ℂ}
    (hR : R ∈ zetaSet π μ) (a : GL (Fin n) F)
    (hR' : ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → R'.eval (RingHom.id ℂ) (qs F s) =
      detPow a (s + ((n : ℂ) - 1) / 2) * R.eval (RingHom.id ℂ) (qs F s)) :
    R' ∈ zetaSet π μ := by
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  obtain ⟨s₁, hs₁⟩ := hR'
  refine ⟨fun Y => Φ (((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Y), v,
    Representation.dual π a ℓ, hΦ.comp_mul_left a⁻¹, smooth_apply_mem _ hℓ a, max s₀ s₁,
    fun s hs => ?_⟩
  rw [zetaIntegral_translate, hZ s ((le_max_left _ _).trans_lt hs),
    hs₁ s ((le_max_right _ _).trans_lt hs)]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem ordDet_diagPow_single [NeZero n] :
    ordDet (Cartan.diagPow F n (Pi.single 0 1)) = 1 := by
  rw [ordDet, Cartan.coe_diagPow, det_diagonal, Finset.prod_eq_single (0 : Fin n)]
  · simp [LocalField.ord_uniformizer (irreducible_uniformizer F)]
  · intro b _ hb
    simp [hb]
  · simp

theorem X_mul_mem_zetaIdeal [NeZero n] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {R : RatFunc ℂ} (hR : R ∈ zetaIdeal π μ) : RatFunc.X * R ∈ zetaIdeal π μ := by
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  refine Submodule.span_induction (p := fun R _ => RatFunc.X * R ∈ zetaIdeal π μ) ?_ ?_ ?_ ?_ hR
  · intro R hR
    set a := Cartan.diagPow F n (Pi.single 0 1)
    have hmem : RatFunc.C c * RatFunc.X * R ∈ zetaSet π μ := by
      refine mem_zetaSet_of_translate μ hR a ?_
      obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C c * RatFunc.X) R
      obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
      refine ⟨s₁, fun s hs => ?_⟩
      rw [hεR _ (qs_ne_zero s) (hs₁ s hs), detPow_eq_qs_zpow, ordDet_diagPow_single, zpow_one,
        qs_add, ← hcdef, RatFunc.eval_mul (f := RingHom.id ℂ) (a := qs F s) (by simp) (by simp),
        RatFunc.eval_C, RatFunc.eval_X]
      simp only [RingHom.id_apply]
      ring
    have : RatFunc.X * R = c⁻¹ • (RatFunc.C c * RatFunc.X * R) := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c' x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem X_inv_mul_mem_zetaIdeal [NeZero n] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {R : RatFunc ℂ} (hR : R ∈ zetaIdeal π μ) : RatFunc.X⁻¹ * R ∈ zetaIdeal π μ := by
  set c : ℂ := qs F (((n : ℂ) - 1) / 2) with hcdef
  have hc : c ≠ 0 := qs_ne_zero _
  refine Submodule.span_induction (p := fun R _ => RatFunc.X⁻¹ * R ∈ zetaIdeal π μ) ?_ ?_ ?_ ?_ hR
  · intro R hR
    set a := Cartan.diagPow F n (Pi.single 0 1)
    have hXinv : ∀ x : ℂ, x ≠ 0 → (RatFunc.X⁻¹ : RatFunc ℂ).eval (RingHom.id ℂ) x = x⁻¹ := by
      intro x hx
      have := eval_div_algebraMap 1 X (x := x) (by simpa using hx)
      rw [map_one, RatFunc.algebraMap_X, one_div] at this
      rw [this]
      simp
    have hmem : RatFunc.C c⁻¹ * RatFunc.X⁻¹ * R ∈ zetaSet π μ := by
      refine mem_zetaSet_of_translate μ hR a⁻¹ ?_
      obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C c⁻¹ * RatFunc.X⁻¹) R
      obtain ⟨ε', hε', hεR'⟩ := exists_eval_mul (RatFunc.C c⁻¹) (RatFunc.X⁻¹ : RatFunc ℂ)
      obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) (lt_min hε hε')
      refine ⟨s₁, fun s hs => ?_⟩
      have hsm := hs₁ s hs
      have hinv : ordDet a⁻¹ = -1 := by
        have h1 := ordDet_mul a⁻¹ a
        rw [inv_mul_cancel, ordDet_diagPow_single] at h1
        have h0 : ordDet (1 : GL (Fin n) F) = 0 := by simp [ordDet, LocalField.ord_one]
        omega
      rw [hεR _ (qs_ne_zero s) (hsm.trans_le (min_le_left _ _)),
        hεR' _ (qs_ne_zero s) (hsm.trans_le (min_le_right _ _)), RatFunc.eval_C,
        hXinv _ (qs_ne_zero s), detPow_eq_qs_zpow, hinv, qs_add, ← hcdef]
      simp only [RingHom.id_apply, _root_.zpow_neg, zpow_one, mul_inv]
      ring
    have : RatFunc.X⁻¹ * R = c • (RatFunc.C c⁻¹ * RatFunc.X⁻¹ * R) := by
      rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c' x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem exists_zetaSet_eq [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F))
    [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧ ∀ R ∈ zetaSet π μ, ∃ (N : ℕ) (P : ℂ[X]),
      R = algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (X ^ N * D) := by
  obtain ⟨s₀, D, hD0, -, h⟩ := exists_zeta_rat hπ μ
  refine ⟨D, hD0, fun R hR => ?_⟩
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₁, hZ⟩ := hR
  obtain ⟨-, N, P, hP⟩ := h Φ hΦ v ℓ hℓ
  refine ⟨N, P, ?_⟩
  obtain ⟨ε, hε, hεs⟩ := exists_qs_of_small (F := F) (max s₀ s₁)
  refine eq_of_eval_eq hε fun x hx hxε => ?_
  obtain ⟨s, hs, rfl⟩ := hεs x hx hxε
  rw [← hZ s ((le_max_right _ _).trans_lt hs), hP s ((le_max_left _ _).trans_lt hs)]

theorem exists_denominator_zetaIdeal [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ R ∈ zetaIdeal π μ, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra := by
  obtain ⟨D, hD0, hD⟩ := exists_zetaSet_eq hπ μ
  have hDne : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h
    rw [h, eval_zero] at hD0
    exact zero_ne_one hD0
  refine ⟨D, hD0, fun R hR => ?_⟩
  refine Submodule.span_induction
    (p := fun R _ => algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) ?_ ?_ ?_ ?_ hR
  · intro R hR
    obtain ⟨N, P, rfl⟩ := hD R hR
    refine mem_laurentSubalgebra_iff.2 ⟨P, N, ?_⟩
    rw [map_mul, map_pow, RatFunc.algebraMap_X]
    have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    field_simp
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [mul_smul_comm]
    exact Subalgebra.smul_mem _ hx c

theorem one_mem_zetaIdeal (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (hπ : IsSmooth π)
    [Nontrivial V] : (1 : RatFunc ℂ) ∈ zetaIdeal π μ := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ v).mem_nhds (one_mem (stabilizerOf π v)))
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hvK : v ∈ fixedVectors π K := fun k hk => hm hk

  obtain ⟨f0, hf0⟩ : ∃ f0 : Module.Dual ℂ (fixedVectors π K), f0 ⟨v, hvK⟩ = 1 := by
    have hne : (⟨v, hvK⟩ : fixedVectors π K) ≠ 0 := fun h => hv (congrArg Subtype.val h)
    have hnot : ¬ ∀ g : Module.Dual ℂ (fixedVectors π K), g ⟨v, hvK⟩ = 0 := fun h =>
      hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    obtain ⟨g, hg⟩ := not_forall.1 hnot
    exact ⟨(g ⟨v, hvK⟩)⁻¹ • g, by simp [hg]⟩
  set ℓ : Module.Dual ℂ V := f0 ∘ₗ fixedProj π hπ hKc hKo with hℓdef
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := fun k hk x => by
    simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, fixedProj_apply_act hπ hKc hKo hk]
  have hℓ : ℓ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hℓK)
  have hℓv : ℓ v = 1 := by
    have : fixedProj π hπ hKc hKo v = ⟨v, hvK⟩ := Subtype.ext (fixedProj_apply_of_mem hπ hKc hKo hvK)
    simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, this, hf0]

  set S : Set (Matrix (Fin n) (Fin n) F) := Units.val '' (K : Set (GL (Fin n) F)) with hSdef
  have hSo : IsOpen S := (Measures.isOpenEmbedding_val F n).isOpenMap _ hKo
  have hSc : IsCompact S := hKc.image Units.continuous_val
  set Φ : Matrix (Fin n) (Fin n) F → ℂ := S.indicator 1 with hΦdef
  have hΦ : IsSchwartzBruhat Φ := by
    refine ⟨?_, HasCompactSupport.intro hSc fun X hX => Set.indicator_of_notMem hX _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro X
    by_cases hX : X ∈ S
    · exact ⟨S, hSo, hX, fun Y hY => by simp [Φ, Set.indicator_of_mem hY, Set.indicator_of_mem hX]⟩
    · exact ⟨Sᶜ, hSc.isClosed.isOpen_compl, hX, fun Y hY => by
        simp [Φ, Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  have hΦg : ∀ g : GL (Fin n) F, Φ (g : Matrix (Fin n) (Fin n) F) =
      (K : Set (GL (Fin n) F)).indicator 1 g := fun g => by
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem hg, hΦdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hg)]
      rfl
    · rw [Set.indicator_of_notMem hg, hΦdef, Set.indicator_of_notMem]
      rintro ⟨g', hg', hgg'⟩
      exact hg (Units.val_injective hgg' ▸ hg')

  have hZ : ∀ s, zetaIntegral μ Φ (matrixCoeff π v ℓ) s = (μ.real (K : Set (GL (Fin n) F)) : ℂ) := by
    intro s
    rw [zetaIntegral]
    have hfun : (fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)) = (K : Set (GL (Fin n) F)).indicator fun _ => (1 : ℂ) := by
      funext g
      rw [hΦg g]
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, matrixCoeff, hvK g hg, hℓv,
          detPow_of_mem_integralGL (congruenceSubgroup_le F n m hg)]
        simp
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
        simp
    rw [hfun, integral_indicator_const _ hKo.measurableSet]
    simp
  have hmem : RatFunc.C (μ.real (K : Set (GL (Fin n) F)) : ℂ) ∈ zetaSet π μ :=
    ⟨Φ, v, ℓ, hΦ, hℓ, 0, fun s _ => by rw [hZ, RatFunc.eval_C]; rfl⟩
  have hpos : (μ.real (K : Set (GL (Fin n) F)) : ℂ) ≠ 0 := by
    have : 0 < μ.real (K : Set (GL (Fin n) F)) :=
      ENNReal.toReal_pos (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩) hKc.measure_lt_top.ne
    exact_mod_cast this.ne'
  have h1 : (1 : RatFunc ℂ) = ((μ.real (K : Set (GL (Fin n) F)) : ℂ))⁻¹ •
      RatFunc.C (μ.real (K : Set (GL (Fin n) F)) : ℂ) := by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← map_mul, inv_mul_cancel₀ hpos, map_one]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem existsUnique_zetaIdeal_eq [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    ∃! P : ℂ[X], P.eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ zetaIdeal π μ ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V := ⟨⟨v, 0, hv⟩⟩
  obtain ⟨D, hD0, hD⟩ := exists_denominator_zetaIdeal hπ μ
  refine existsUnique_eq_laurent_div _ (fun R hR => X_mul_mem_zetaIdeal μ hR)
    (fun R hR => X_inv_mul_mem_zetaIdeal μ hR) (one_mem_zetaIdeal μ hπ.1) ⟨D, ?_, hD⟩
  intro h
  rw [h, eval_zero] at hD0
  exact zero_ne_one hD0

omit [BorelSpace (GL (Fin n) F)] in
theorem zetaIdeal_le_smul (μ : Measure (GL (Fin n) F)) {c : NNReal} (hc : c ≠ 0) :
    zetaIdeal π μ ≤ zetaIdeal π (c • μ) := by
  refine Submodule.span_le.2 fun R hR => ?_
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hmem : RatFunc.C ((c : ℝ) : ℂ) * R ∈ zetaSet π (c • μ) := by
    obtain ⟨ε, hε, hεR⟩ := exists_eval_mul (RatFunc.C ((c : ℝ) : ℂ)) R
    obtain ⟨s₁, hs₁⟩ := exists_re_of_norm_qs_lt (F := F) hε
    refine ⟨Φ, v, ℓ, hΦ, hℓ, max s₀ s₁, fun s hs => ?_⟩
    rw [hεR _ (qs_ne_zero s) (hs₁ s ((le_max_right _ _).trans_lt hs)), RatFunc.eval_C,
      ← hZ s ((le_max_left _ _).trans_lt hs), zetaIntegral, zetaIntegral,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    rfl
  have h : R = ((c : ℝ) : ℂ)⁻¹ • (RatFunc.C ((c : ℝ) : ℂ) * R) := by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc',
      map_one, one_mul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem zetaIdeal_eq_of_isHaarMeasure (μ ν : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    [ν.IsHaarMeasure] : zetaIdeal π μ = zetaIdeal π ν := by
  have key : ∀ (μ ν : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] [ν.IsHaarMeasure],
      zetaIdeal π μ ≤ zetaIdeal π ν := by
    intro μ ν _ _
    rw [Measure.isMulLeftInvariant_eq_smul ν μ]
    exact zetaIdeal_le_smul μ (Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ).ne'
  exact le_antisymm (key μ ν) (key ν μ)

variable (π) in

def LPolynomial : ℂ[X] := by
  classical
  exact if h : ∃ P : ℂ[X], P.eval 0 = 1 ∧ ∀ R : RatFunc ℂ,
      R ∈ zetaIdeal π (Measure.haar : Measure (GL (Fin n) F)) ↔
        ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P then h.choose else 1

variable (π) in

def LFunction (s : ℂ) : ℂ :=
  ((LPolynomial π).eval (qs F s))⁻¹

theorem LPolynomial_spec [NeZero n] [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    (LPolynomial π).eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ zetaIdeal π μ ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π) := by
  classical
  have h := (existsUnique_zetaIdeal_eq hπ (Measure.haar : Measure (GL (Fin n) F))).exists
  rw [LPolynomial, dif_pos h]
  obtain ⟨h0, hiff⟩ := h.choose_spec
  refine ⟨h0, fun R => ?_⟩
  rw [zetaIdeal_eq_of_isHaarMeasure μ Measure.haar]
  exact hiff R

end GodementJacquet

end GroundTheory.Automorphic
