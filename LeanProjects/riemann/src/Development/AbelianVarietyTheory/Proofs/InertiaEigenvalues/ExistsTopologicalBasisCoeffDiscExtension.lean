import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscCoeff

theorem isLocalization_int (l : ℕ) {B : Type} [CommRing B] (u : B) (ρ : ℝ≥0) :
    IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (l : ℤ))) (PreDisc l u ρ) := by
  have h : Algebra.algebraMapSubmonoid B (Submonoid.powers (l : ℤ)) = Submonoid.powers (l : B) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rw [h]; infer_instance

instance (l : ℕ) {B : Type} [CommRing B] (u : B) (ρ : ℝ≥0) :
    IsLocalizedModule (Submonoid.powers (l : ℤ)) (IsScalarTower.toAlgHom ℤ B (PreDisc l u ρ)).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr (isLocalization_int l u ρ)

variable {l : ℕ}

theorem exists_eq {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} (y : PreDisc l u ρ) :
    ∃ (a : B) (n : ℕ), y = algebraMap B (PreDisc l u ρ) a * IsLocalization.Away.invSelf (l : B) ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : B) y
  refine ⟨a, n, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem natCast_mul_invSelf {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} :
    (l : PreDisc l u ρ) * IsLocalization.Away.invSelf (l : B) = 1 := by
  rw [← map_natCast (algebraMap B (PreDisc l u ρ)), IsLocalization.Away.mul_invSelf]

theorem pow_mul_mono {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} (a : B) (n : ℕ) :
    (l : PreDisc l u ρ) ^ n * (algebraMap B (PreDisc l u ρ) a * IsLocalization.Away.invSelf (l : B) ^ n) =
      algebraMap B (PreDisc l u ρ) a := by
  rw [mul_left_comm, ← mul_pow, natCast_mul_invSelf, one_pow, mul_one]

variable (l) {A S : Type} [CommRing A] [CommRing S] (s : S →+* A) (u : S) (ρ : ℝ≥0) (c : A →+ S)

def preCoeff : PreDisc l (s u) ρ →ₗ[ℤ] PreDisc l u ρ :=
  IsLocalizedModule.lift (Submonoid.powers (l : ℤ)) (IsScalarTower.toAlgHom ℤ A (PreDisc l (s u) ρ)).toLinearMap
    ((IsScalarTower.toAlgHom ℤ S (PreDisc l u ρ)).toLinearMap.comp c.toIntLinearMap)
    (IsLocalizedModule.map_units (IsScalarTower.toAlgHom ℤ S (PreDisc l u ρ)).toLinearMap)

variable {l s u ρ c}

theorem preCoeff_alg (a : A) :
    preCoeff l s u ρ c (algebraMap A _ a) = algebraMap S (PreDisc l u ρ) (c a) :=
  IsLocalizedModule.lift_apply _ _ _ _ a

theorem preCoeff_mono (a : A) (n : ℕ) :
    preCoeff l s u ρ c (algebraMap A _ a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap S (PreDisc l u ρ) (c a) * IsLocalization.Away.invSelf (l : S) ^ n := by
  have hl : IsUnit (l : PreDisc l u ρ) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u ρ) (l : S)
    rwa [map_natCast] at this
  refine (hl.pow n).mul_left_cancel ?_
  rw [pow_mul_mono]
  have e : ((l : ℤ) ^ n) • (algebraMap A (PreDisc l (s u) ρ) a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap A _ a := by
    rw [zsmul_eq_mul]; push_cast; exact pow_mul_mono a n
  have e2 := congrArg (preCoeff l s u ρ c) e
  rw [LinearMap.map_smul, zsmul_eq_mul, preCoeff_alg] at e2
  push_cast at e2
  exact e2

variable (hc : ∀ a x, c (s a * x) = a * c x)
include hc

theorem norm_preCoeff_le (y : PreDisc l (s u) ρ) : ‖preCoeff l s u ρ c y‖ ≤ ‖y‖ := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := (norm_nonneg y).trans_lt hr
  have hy := mem_ball_of_gauge_lt l (s u) ρ hr
  suffices h : ∀ x ∈ ball l (s u) ρ r, ∀ a : A, preCoeff l s u ρ c (a • x) ∈ ball l u ρ r by
    have h1 := h y hy 1
    rw [one_smul] at h1
    exact gauge_le l u ρ hr0 h1
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, k, h1, rfl⟩ := hx
    intro a'
    have e : a' • (algebraMap A (PreDisc l (s u) ρ) ((l : A) ^ a * s u ^ b) * IsLocalization.Away.invSelf (l : A) ^ k) =
        algebraMap A _ (s ((l : S) ^ a * u ^ b) * a') * IsLocalization.Away.invSelf (l : A) ^ k := by
      simp only [Algebra.smul_def, map_mul, map_pow, map_natCast]; ring
    have e2 : algebraMap S (PreDisc l u ρ) (c (s ((l : S) ^ a * u ^ b) * a')) * IsLocalization.Away.invSelf (l : S) ^ k =
        c a' • (algebraMap S (PreDisc l u ρ) ((l : S) ^ a * u ^ b) * IsLocalization.Away.invSelf (l : S) ^ k) := by
      rw [hc, Algebra.smul_def, map_mul]; ring
    rw [e, preCoeff_mono, e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, b, k, h1, rfl⟩)
  | zero => intro a'; rw [smul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a'; rw [smul_add, map_add]; exact add_mem (hx a') (hy a')
  | smul a x _ hx => intro a'; rw [smul_smul]; exact hx _

theorem continuous_preCoeff : Continuous (preCoeff l s u ρ c).toAddMonoidHom :=
  AddMonoidHomClass.continuous_of_bound (preCoeff l s u ρ c).toAddMonoidHom 1
    fun y => (norm_preCoeff_le hc y).trans (one_mul _).ge

theorem preCoeff_mul (p : PreDisc l u ρ) (q : PreDisc l (s u) ρ) :
    preCoeff l s u ρ c (preMap l u ρ (s u) ρ s p * q) = p * preCoeff l s u ρ c q := by
  obtain ⟨w, m, rfl⟩ := exists_eq p
  obtain ⟨a, n, rfl⟩ := exists_eq q
  have e : preMap l u ρ (s u) ρ s (algebraMap S _ w * IsLocalization.Away.invSelf (l : S) ^ m) *
      (algebraMap A _ a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap A (PreDisc l (s u) ρ) (s w * a) * IsLocalization.Away.invSelf (l : A) ^ (m + n) := by
    rw [map_mul, map_pow, preMap_alg, preMap_inv, map_mul]; ring
  rw [e, preCoeff_mono, preCoeff_mono, hc, map_mul]; ring

variable (l s u ρ c)

def discCoeff : Disc l (s u) ρ →+ Disc l u ρ :=
  (preCoeff l s u ρ c).toAddMonoidHom.completion (continuous_preCoeff hc)

variable {l s u ρ c}

theorem discCoeff_ofPre (y : PreDisc l (s u) ρ) :
    discCoeff l s u ρ c hc (ofPre l (s u) ρ y) = ofPre l u ρ (preCoeff l s u ρ c y) :=
  AddMonoidHom.completion_coe _ _ y

theorem continuous_discCoeff : Continuous (discCoeff l s u ρ c hc) :=
  AddMonoidHom.continuous_completion _ _

theorem discCoeff_toDisc (a : A) :
    discCoeff l s u ρ c hc (toDisc l (s u) ρ a) = toDisc l u ρ (c a) :=
  (discCoeff_ofPre hc _).trans (congrArg (ofPre l u ρ) (preCoeff_alg a))

theorem norm_discCoeff_le (y : Disc l (s u) ρ) : ‖discCoeff l s u ρ c hc y‖ ≤ ‖y‖ := by
  refine (denseRange_ofPre l (s u) ρ).induction_on y
    (isClosed_le (continuous_norm.comp (continuous_discCoeff hc)) continuous_norm) fun q => ?_
  rw [discCoeff_ofPre, norm_ofPre, norm_ofPre]
  exact norm_preCoeff_le hc q

theorem discCoeff_mul {j : Disc l u ρ →+* Disc l (s u) ρ} (hj : IsDiscMap s j) (x : Disc l u ρ)
    (y : Disc l (s u) ρ) : discCoeff l s u ρ c hc (j x * y) = x * discCoeff l s u ρ c hc y := by
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 fun x => (hj.norm_le x).trans (one_mul _).ge
  have hdc : Continuous (discCoeff l s u ρ c hc) := continuous_discCoeff hc
  have e : j.comp (ofPre l u ρ) = (ofPre l (s u) ρ).comp (preMap l u ρ (s u) ρ s) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]
      rw [preMap_alg]
      exact hj.ext a)
  refine (denseRange_ofPre l u ρ).induction_on x
    (isClosed_eq (hdc.comp (hjc.mul continuous_const)) (continuous_id.mul continuous_const)) fun p => ?_
  refine (denseRange_ofPre l (s u) ρ).induction_on y
    (isClosed_eq (hdc.comp (continuous_const.mul continuous_id)) (continuous_const.mul hdc)) fun q => ?_
  rw [show j (ofPre l u ρ p) = ofPre l (s u) ρ (preMap l u ρ (s u) ρ s p) from RingHom.congr_fun e p,
    ← map_mul, discCoeff_ofPre, discCoeff_ofPre, ← map_mul, preCoeff_mul hc]

end GlobalTheory.BSP.DiscCoeff

open GlobalTheory.BSP.DiscCoeff in

theorem GlobalTheory.BSP.exists_discCoeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) := by
  intro l _ K bk A _ s ι TB ρ _ _ j hj
  exact ⟨fun i => discCoeff l s X ρ (TB.c i) (TB.c_mul i), fun i a => discCoeff_toDisc (TB.c_mul i) a,
    fun i x y => discCoeff_mul (TB.c_mul i) hj x y, fun i y => norm_discCoeff_le (TB.c_mul i) y⟩
