import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecayAtCusp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormEqZeroOfPeriodicOfBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionProperties

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Positivity

noncomputable def segPt (τ : ℍ) (t : ℝ) : ℍ :=
  ⟨Complex.I + ((Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) : ℂ) * ((τ : ℂ) - Complex.I), by
    have h0 := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.1
    have h1 := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.2
    have h2 := τ.im_pos
    simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
    rcases h1.eq_or_lt with h | h
    · rw [h]; linarith
    · nlinarith [mul_nonneg h0 h2.le]⟩

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eichler_mem_degreeLT_succ (w : ℕ) (g : ℍ → ℂ) (τ : ℍ) :
    _root_.GlobalTheory.HeckeFamilyMatrices.eichler w g τ ∈ ℂ[X]_(w + 1) := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [_root_.GlobalTheory.EichlerChange.coeff_eichler, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma map_conj_mem_degreeLT {n : ℕ} {p : ℂ[X]} (hp : p ∈ ℂ[X]_n) :
    p.map (starRingEnd ℂ) ∈ ℂ[X]_n := by
  rw [Polynomial.mem_degreeLT] at hp ⊢
  rwa [Polynomial.degree_map]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma sl_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  simpa [UpperHalfPlane.denom] using h

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eval_eq_denom_pow_mul_eval_of_slP_invariant (w : ℕ) (V : ℍ → ℂ[X]) (γ : SL(2, ℤ)) (τ : ℍ)
    (hmem : V (γ • τ) ∈ ℂ[X]_(w + 1))
    (hrel : _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ) :
    eval (τ : ℂ) (V τ) =
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * eval ((γ • τ : ℍ) : ℂ) (V (γ • τ)) := by
  rw [← hrel, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ _ hmem (sl_denom_ne_zero γ τ)]
  congr 2
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [_root_.GlobalTheory.HeckeFamilyMatrices.mat]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma im_sl_smul_eq_im_div_normSq_denom (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im = τ.im / Complex.normSq (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma continuous_eval_of_continuous_coeff_of_degree_le (w : ℕ) (V : ℍ → ℂ[X])
    (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1)) (hc : ∀ n, Continuous fun τ => (V τ).coeff n) :
    Continuous fun τ : ℍ => eval (τ : ℂ) (V τ) := by
  have h : (fun τ : ℍ => eval (τ : ℂ) (V τ)) =
      fun τ => ∑ i ∈ Finset.range (w + 1), (V τ).coeff i * (τ : ℂ) ^ i := by
    funext τ
    apply eval_eq_sum_range'
    by_cases h0 : V τ = 0
    · simp [h0]
    · have := hmem τ
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt h0).2 this
  rw [h]
  exact continuous_finset_sum _ fun i _ => (hc i).mul (continuous_coe.pow i)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma exists_norm_eval_le_mul_im_rpow_of_slP_invariant (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (w : ℕ)
    (V : ℍ → ℂ[X]) (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1))
    (hc : ∀ n, Continuous fun τ => (V τ).coeff n)
    (hrel : ∀ γ ∈ Γ, ∀ τ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ)
    (hdecay : ∀ g : SL(2, ℤ), Filter.Tendsto
      (fun τ => ‖eval ((g • τ : ℍ) : ℂ) (V (g • τ))‖ * (g • τ).im ^ (-(w : ℝ) / 2))
      atImInfty (nhds 0)) :
    ∃ C, ∀ τ : ℍ, ‖eval (τ : ℂ) (V τ)‖ ≤ C * τ.im ^ ((w : ℝ) / 2) := by
  have hinv : ∀ γ ∈ Γ, ∀ τ : ℍ,
      ‖eval ((γ • τ : ℍ) : ℂ) (V (γ • τ))‖ * (γ • τ).im ^ (-(w : ℝ) / 2) =
        ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    intro γ hγ τ
    have he := eval_eq_denom_pow_mul_eval_of_slP_invariant w V γ τ (hmem _) (hrel γ hγ τ)
    have hD := sl_denom_ne_zero γ τ
    set D := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hDdef
    have hDpos : 0 < ‖D‖ := norm_pos_iff.2 hD
    have hx : (‖D‖ ^ (2 : ℕ)) ^ (-(w : ℝ) / 2) = (‖D‖ ^ w)⁻¹ := by
      rw [← Real.rpow_natCast ‖D‖ 2, ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (-(w : ℝ) / 2) = -(w : ℝ) by push_cast; ring,
        Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [he, im_sl_smul_eq_im_div_normSq_denom, ← hDdef, Real.div_rpow τ.im_pos.le (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, hx, norm_mul, norm_pow]
    have hw : 0 < ‖D‖ ^ w := pow_pos hDpos w
    field_simp
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
    (f := fun τ : ℍ => ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2))
    (((continuous_eval_of_continuous_coeff_of_degree_le w V hmem hc).norm).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inl τ.im_pos.ne'))
    le_rfl (fun g => by simpa using (hdecay g).isBigO_one ℝ) (Γ := Γ) hinv
  refine ⟨C, fun τ => ?_⟩
  have h1 := hC τ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by positivity)] at h1
  have hpos : 0 < τ.im ^ ((w : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  calc ‖eval (τ : ℂ) (V τ)‖
      = ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) * τ.im ^ ((w : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add τ.im_pos]
        simp [neg_div]
    _ ≤ C * τ.im ^ ((w : ℝ) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eq_zero_of_eichler_conj_slash_relation (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hΓ : Γ.FiniteIndex) (hk : 3 ≤ k)
    (f h : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k) (p : ℂ[X])
    (hp : p ∈ ℂ[X]_(k - 1))
    (hrel : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - p) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p) :
    h = 0 := by
  set V : ℍ → ℂ[X] := fun τ => _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
    map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p with hV
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have hp' : p ∈ ℂ[X]_(k - 2 + 1) := by rw [← hk1]; exact hp
  have hmem : ∀ τ, V τ ∈ ℂ[X]_(k - 2 + 1) := fun τ =>
    sub_mem (sub_mem (eichler_mem_degreeLT_succ _ _ _)
      (map_conj_mem_degreeLT (eichler_mem_degreeLT_succ _ _ _))) hp'
  have hcf : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k, ∀ n : ℕ,
      Continuous fun τ => (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ).coeff n := by
    intro g n
    simp_rw [_root_.GlobalTheory.EichlerChange.coeff_eichler]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun τ => ?_)
    exact ((_root_.GlobalTheory.EichlerChange.hasDerivAt_ecoef (k - 2) g (CuspFormClass.holo g) n τ
      τ.im_pos).continuousAt).comp continuous_coe.continuousAt
  have hc : ∀ n, Continuous fun τ => (V τ).coeff n := by
    intro n
    simp only [hV, coeff_sub, coeff_map]
    exact ((hcf f n).sub (Complex.continuous_conj.comp (hcf h n))).sub continuous_const
  have hrel' : ∀ γ ∈ Γ, ∀ τ,
      _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ :=
    fun γ hγ τ => hrel ⟨γ, hγ⟩ τ
  have hdecay := _root_.GlobalTheory.HeckeFamilyMatrices.Decay.decay_at_cusp Γ k hΓ hk f h p hp hrel
  have hw : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  obtain ⟨C, hC⟩ := exists_norm_eval_le_mul_im_rpow_of_slP_invariant Γ (k - 2) V hmem hc hrel'
    (by rw [hw]; exact hdecay)
  obtain ⟨n, hn, -, hTn⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero ModularGroup.T
  refine _root_.GlobalTheory.EichlerPositivity.cuspForm_eq_zero_of_periodic_of_bound Γ k hΓ hk f h p n C hn (fun τ => ?_)
    (fun τ => by rw [← hw]; exact hC τ)
  have hT : ModularGroup.T ^ n • τ = (n : ℝ) +ᵥ τ := by
    rw [← zpow_natCast, modular_T_zpow_smul]; simp
  have he := eval_eq_denom_pow_mul_eval_of_slP_invariant (k - 2) V (ModularGroup.T ^ n) τ (hmem _) (hrel' _ hTn τ)
  have h10 : ((ModularGroup.T ^ n) 1 0 : ℤ) = 0 ∧ ((ModularGroup.T ^ n) 1 1 : ℤ) = 1 := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]; simp
  rw [h10.1, h10.2] at he
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_one, one_pow, one_mul, hT] at he
  exact he.symm

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in

theorem _root_.GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N →
    Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)),
    _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f - _root_.GlobalTheory.HeckeFamilyMatrices.cj (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h) ∈
      _root_.GlobalTheory.HeckeFamilyMatrices.B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  intro N Γ k _ _ hΓ hk f h hB
  unfold _root_.GlobalTheory.HeckeFamilyMatrices.B1 at hB
  obtain ⟨⟨q, hq⟩, hqe⟩ := hB
  have hcoc : ∀ γ : Γ, _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) q - q =
      _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f γ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h γ) := fun γ => by
    have := congrFun hqe γ
    simpa [_root_.GlobalTheory.HeckeFamilyMatrices.cj] using this
  have hper : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k,
      ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑g γ =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
            (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ := fun g =>
    (_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k (by omega) (CuspForm.toModularFormₗ g)).2
  have hmemE : ∀ (g : ℍ → ℂ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ ∈ ℂ[X]_(k - 2 + 1) :=
    fun g τ => eichler_mem_degreeLT_succ _ _ _
  have hconj : ∀ p ∈ ℂ[X]_(k - 2 + 1), ∀ γ : SL(2, ℤ),
      map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) p) =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (map (starRingEnd ℂ) p) :=
    fun p hp γ =>
      (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) 1 p hp).2.2.2
  have hcc : ∀ p : ℂ[X], map (starRingEnd ℂ) (map (starRingEnd ℂ) p) = p := fun p => by
    ext n; simp [coeff_map]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have rel1 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - q := by
    intro γ τ
    have h1 := hcoc γ
    rw [hper f γ τ, hper h γ τ, Polynomial.map_sub, hconj _ (hmemE _ _)] at h1
    rw [map_sub, map_sub]
    linear_combination -h1
  have rel2 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ) - -map (starRingEnd ℂ) q := by
    intro γ τ
    have h2 := congrArg (map (starRingEnd ℂ)) (rel1 γ τ)
    rw [hconj _ (sub_mem (sub_mem (hmemE _ _) (map_conj_mem_degreeLT (hmemE _ _))) hq)] at h2
    simp only [Polynomial.map_sub, hcc] at h2
    have hneg : _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q =
        -(map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) - map (starRingEnd ℂ) q) := by ring
    rw [hneg, map_neg, h2]
    ring
  have hq' : q ∈ ℂ[X]_(k - 1) := by rw [hk1]; exact hq
  exact ⟨eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk h f _
      (neg_mem (map_conj_mem_degreeLT hq')) rel2,
    eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk f h q hq' rel1⟩

end GlobalTheory.HeckeFamilyMatrices.Positivity
