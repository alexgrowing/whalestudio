import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.ConstantTerm
import GroundTheory.AutomorphicForms.GL2Classical.Periodic
import GroundTheory.AutomorphicForms.GL2Classical.Growth
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem unipMatrix_eval {R : Type*} [CommRing R] (y : R) :
    unipMatrix (n := 2) (r := 1) (fun _ => y) 0 0 = 1 ∧ unipMatrix (n := 2) (r := 1) (fun _ => y) 0 1 = y ∧
      unipMatrix (n := 2) (r := 1) (fun _ => y) 1 0 = 0 ∧
        unipMatrix (n := 2) (r := 1) (fun _ => y) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [unipMatrix_apply] <;> simp

theorem conj_unipFin_apply (w : FiniteAdelicGL ℚ 2) (y : 𝔸f) (i j : Fin 2) :
    ((w⁻¹ * unipFin y * w : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) i j =
      (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j +
        y * (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) i 0 *
          (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 j) := by
  have hVW : ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) * (w : Matrix (Fin 2) (Fin 2) 𝔸f) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hij := congrFun (congrFun hVW i) j
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hij
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval y
  rw [Units.val_mul, Units.val_mul]
  change (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) *
    unipMatrix (n := 2) (r := 1) (fun _ => y) * (w : Matrix (Fin 2) (Fin 2) 𝔸f)) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Fin.sum_univ_two, u00, u01, u10, u11]
  linear_combination hij

theorem unipFin_inv (y : 𝔸f) : (unipFin y)⁻¹ = unipFin (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [unipFin, unipFin, ← unipGL_add]
  convert unipGL_zero (n := 2) (r := 1) (R := 𝔸f) using 2
  funext _
  simp

variable (N) in

theorem exists_level_conj (w : FiniteAdelicGL ℚ 2) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ levelIdeal M, w⁻¹ * unipFin y * w ∈ Gamma0Level N := by
  set e : Fin 2 × Fin 2 → 𝔸f := fun p => ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) p.1 0 *
    (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 p.2
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact (K := ℚ)
    (Set.finite_range e).isCompact
  set z : ℤ := Rat.ringOfIntegersEquiv d
  have hz0 : z ≠ 0 := by
    intro h
    exact hd0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ d = z := (Rat.ringOfIntegersEquiv_apply_coe d).symm
  set D : ℕ := z.natAbs
  have hD : 0 < D := Int.natAbs_pos.2 hz0
  have hDe : ∀ p, (D : 𝔸f) * e p ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro p
    have h1 := hd (e p) ⟨p, rfl⟩
    rw [hdz, map_intCast] at h1
    rcases Int.natAbs_eq z with h | h
    · have hD1 : ((D : ℕ) : ℤ) = z := by simp only [D]; omega
      rw [show (D : 𝔸f) = (z : 𝔸f) by rw [← Int.cast_natCast, hD1]]
      exact h1
    · have hD2 : ((D : ℕ) : ℤ) = -z := by simp only [D]; omega
      rw [show (D : 𝔸f) = -(z : 𝔸f) by rw [← Int.cast_natCast, hD2, Int.cast_neg], neg_mul]
      exact neg_mem h1
  refine ⟨N * D, Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hD, fun y hy => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hy
  have hye : ∀ p, ((N * D : ℕ) : 𝔸f) * t * e p ∈ levelIdeal N := fun p =>
    ⟨t * ((D : 𝔸f) * e p), mul_mem ht (hDe p), by push_cast; ring⟩
  have hye' : ∀ p, -(((N * D : ℕ) : 𝔸f) * t) * e p ∈ levelIdeal N := fun p => by
    obtain ⟨s, hs, hs'⟩ := hye p
    exact ⟨-s, neg_mem hs, by rw [neg_mul, hs', mul_neg]⟩
  have hinv : (w⁻¹ * unipFin (((N * D : ℕ) : 𝔸f) * t) * w)⁻¹ =
      w⁻¹ * unipFin (-(((N * D : ℕ) : 𝔸f) * t)) * w := by
    rw [show (w⁻¹ * unipFin (((N * D : ℕ) : 𝔸f) * t) * w)⁻¹ =
      w⁻¹ * (unipFin (((N * D : ℕ) : 𝔸f) * t))⁻¹ * w by group, unipFin_inv]
  refine ⟨(mem_integralFiniteGL_iff ℚ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · rw [conj_unipFin_apply]
    refine add_mem ?_ (levelIdeal_subset N (hye (i, j)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [hinv, conj_unipFin_apply]
    refine add_mem ?_ (levelIdeal_subset N (hye' (i, j)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [conj_unipFin_apply, Matrix.one_apply_ne (by decide), zero_add]
    exact hye (1, 0)

theorem constantTerm_realEmb_mul_finEmb_of_conj {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (h : GL (Fin 2) ℝ) {w : FiniteAdelicGL ℚ 2} {M : ℕ} [NeZero M]
    (hconj : ∀ y ∈ levelIdeal M, w⁻¹ * unipFin y * w ∈ Gamma0Level N) :
    constantTerm 1 φ (realEmb h * finEmb ℚ 2 w) =
      levelConstant M • ∫ t in (0 : ℝ)..M, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) := by
  set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h) * finEmb ℚ 2 w)
  rw [constantTerm_eq_setIntegral_adele hφ.isLeftInvariant (isAddFundamentalDomain_levelDomain M)]
  have heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)))
      (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain M) := by
    intro x hx
    have e : unipAdele x * (realEmb h * finEmb ℚ 2 w) =
        realEmb (unipReal (RationalIdeles.realEquiv x.1) * h) * finEmb ℚ 2 w *
          finEmb ℚ 2 (w⁻¹ * unipFin x.2 * w) := by
      rw [unipAdele_eq]
      apply (prodEquiv ℚ 2).injective
      simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
      rw [Prod.mk.injEq]
      exact ⟨rfl, by group⟩
    simp only [G]
    rw [e, hφ.right_level _ _ (hconj _ hx.2)]
  rw [setIntegral_congr_fun (measurableSet_levelDomain M) heq]
  set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) M
  calc ∫ x in levelDomain M, G (RationalIdeles.realEquiv x.1) ∂adeleMeasure ℚ
      = ∫ x in (A ×ˢ levelIdeal M : Set (InfiniteAdeleRing ℚ × 𝔸f)), G (RationalIdeles.realEquiv x.1)
          ∂((infiniteAdeleMeasure ℚ).prod (finiteAdeleMeasure ℚ)) := rfl
    _ = (finiteAdeleMeasure ℚ (levelIdeal M)).toReal •
          ∫ x in A, G (RationalIdeles.realEquiv x) ∂infiniteAdeleMeasure ℚ := by
        have hf := integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A)
          (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal M))
          (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))
        rw [← Measure.prod_restrict]
        refine hf.trans ?_
        rw [measureReal_restrict_apply_univ, measureReal_def]
    _ = (finiteAdeleMeasure ℚ (levelIdeal M)).toReal •
          ∫ t in Set.Ico (0 : ℝ) M, G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by
        congr 1
        exact (realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ)
          G (Set.Ico (0 : ℝ) M)).symm
    _ = levelConstant M • ∫ t in (0 : ℝ)..M, G t := by
        rw [map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
          intervalIntegral.integral_of_le (Nat.cast_nonneg M), integral_Ico_eq_integral_Ioo,
          ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]

def unipRat (q : ℚ) : GL (Fin 2) ℚ := unipGL (n := 2) (r := 1) fun _ => q

theorem toReal_unipRat (q : ℚ) : toReal (unipRat q) = unipReal q := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((unipMatrix (n := 2) (r := 1) (fun _ => q) a b : ℚ) : ℝ) =
    unipMatrix (n := 2) (r := 1) (fun _ => (q : ℝ)) a b
  rw [unipMatrix_apply, unipMatrix_apply]
  split_ifs <;> simp

theorem finiteDiagonal_unipRat (q : ℚ) :
    finiteDiagonal ℚ 2 (unipRat q) = unipFin (algebraMap ℚ 𝔸f q) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change algebraMap ℚ 𝔸f (unipMatrix (n := 2) (r := 1) (fun _ => q) a b) =
    unipMatrix (n := 2) (r := 1) (fun _ => algebraMap ℚ 𝔸f q) a b
  rw [unipMatrix_apply, unipMatrix_apply]
  split_ifs <;> simp

theorem epsilon_mul_unipRat_mul_epsilon (q : ℚ) : epsilon * unipRat q * epsilon = unipRat (-q) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, Units.val_mul]
  change (!![-1, 0; 0, 1] * unipMatrix (n := 2) (r := 1) (fun _ => q) * !![-1, 0; 0, 1] :
    Matrix (Fin 2) (Fin 2) ℚ) a b = unipMatrix (n := 2) (r := 1) (fun _ => -q) a b
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval q
  obtain ⟨v00, v01, v10, v11⟩ := unipMatrix_eval (-q)
  have hm : (!![-1, 0; 0, 1] * !![1, q; 0, 1] * !![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) =
      !![1, -q; 0, 1] := by
    simp
  rw [Matrix.eta_fin_two (unipMatrix (n := 2) (r := 1) (fun _ => q)),
    Matrix.eta_fin_two (unipMatrix (n := 2) (r := 1) (fun _ => -q)), u00, u01, u10, u11, v00, v01,
    v10, v11, hm]

theorem unipReal_mul_borelGL (t : ℝ) (z : ℍ) : unipReal t * borelGL z = borelGL (t +ᵥ z) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [Units.val_mul, coe_borelGL, coe_borelGL]
  change (unipMatrix (n := 2) (r := 1) (fun _ => t) * !![z.im, z.re; 0, 1]) a b = _
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval t
  have hre : (t +ᵥ z).re = t + z.re := vadd_re t z
  have him : (t +ᵥ z).im = z.im := vadd_im t z
  fin_cases a <;> fin_cases b <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, u00, u01, u10, u11, hre, him]; try ring)

theorem det_unipReal (t : ℝ) : (unipReal t).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (unipMatrix (n := 2) (r := 1) (fun _ => t)).det = 1
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval t
  rw [Matrix.det_fin_two, u00, u01, u10, u11]
  ring

theorem IsWeightLevel.apply_realEmb_mul_finiteDiagonal {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : IsWeightLevel N k φ) (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) {u : FiniteAdelicGL ℚ 2}
    (hu : u ∈ Gamma0Level N) :
    φ (realEmb h * finEmb ℚ 2 (finiteDiagonal ℚ 2 γ * u)) = φ (realEmb ((toReal γ)⁻¹ * h)) := by
  rw [map_mul, ← mul_assoc, hφ.right_level _ _ hu, ← hφ.isLeftInvariant γ⁻¹]
  congr 1
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
    Prod.inv_mk, inv_one, mul_one, one_mul, inv_mul_cancel]

theorem archLift_unipReal_mul (F : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (t : ℝ) :
    archLift k F (unipReal t * h) =
      (denom h ((UpperHalfPlane.I : ℍ) : ℂ) / (‖denom h ((UpperHalfPlane.I : ℍ) : ℂ)‖ : ℂ)) ^ (-k) *
        ((Real.sqrt (h • UpperHalfPlane.I).im : ℂ) ^ k * F (t +ᵥ (h • UpperHalfPlane.I))) := by
  conv_lhs => rw [eq_borelGL_mul_kGL hpos, ← mul_assoc, unipReal_mul_borelGL]
  rw [archLift_mul_kGL k F (det_borelGL_pos _), archLift_borelGL, vadd_im]

theorem denom_unipReal (t : ℝ) (w : ℂ) : denom (unipReal t) w = 1 := by
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval t
  rw [denom]
  change ((unipMatrix (n := 2) (r := 1) (fun _ => t) 1 0 : ℝ) : ℂ) * w +
    ((unipMatrix (n := 2) (r := 1) (fun _ => t) 1 1 : ℝ) : ℂ) = 1
  rw [u10, u11]
  simp

theorem unipReal_smul (t : ℝ) (z : ℍ) : unipReal t • z = t +ᵥ z := by
  have hpos : 0 < (unipReal t).det.val := by rw [det_unipReal]; exact one_pos
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hpos, denom_unipReal, div_one, num, coe_vadd]
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval t
  change ((unipMatrix (n := 2) (r := 1) (fun _ => t) 0 0 : ℝ) : ℂ) * z +
    ((unipMatrix (n := 2) (r := 1) (fun _ => t) 0 1 : ℝ) : ℂ) = _
  rw [u00, u01]
  simp [add_comm]

theorem archLift_mul_left (f : ℍ → ℂ) {δ y : GL (Fin 2) ℝ} (hδ : 0 < δ.det.val) (hy : 0 < y.det.val) :
    (δ.det.val : ℂ) ^ (k - 1) * archLift k f (δ * y) =
      (Real.sqrt δ.det.val : ℂ) ^ k * archLift k (f ∣[k] δ) y := by
  rw [archLift, archLift, slash_apply, σ_of_det_pos hδ, abs_of_pos hδ, map_mul, Units.val_mul,
    Real.sqrt_mul hδ.le, Complex.ofReal_mul, mul_zpow, mul_smul, denom_mul_of_det_pos _ hy, mul_zpow]
  ring

theorem slash_periodic {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {δ : GL (Fin 2) ℚ} (q : ℚ)
    (hmem : finiteDiagonal ℚ 2 (δ * unipRat q * δ⁻¹) ∈ Gamma0Level N) (z : ℍ) :
    (f ∣[k] toReal δ) ((q : ℝ) +ᵥ z) = (f ∣[k] toReal δ) z := by
  have hdet : 0 < ((δ * unipRat q * δ⁻¹).det.val : ℚ) := by
    have h1 : (unipRat q).det.val = 1 := by
      have := det_unipReal (q : ℝ)
      rw [← toReal_unipRat, det_toReal] at this
      exact_mod_cast this
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, h1, mul_one, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero _)]
    exact one_pos
  obtain ⟨s, hs, hsδ⟩ := exists_mem_Gamma0_of_mem N hmem hdet
  have hreal : Matrix.SpecialLinearGroup.mapGL ℝ s * toReal δ = toReal δ * unipReal q := by
    rw [← toReal_mapGL, hsδ, map_mul, map_mul, map_inv, toReal_unipRat, inv_mul_cancel_right]
  have hper : (f ∣[k] toReal δ) ∣[k] unipReal q = f ∣[k] toReal δ := by
    rw [← SlashAction.slash_mul, ← hreal, SlashAction.slash_mul,
      hf _ (Subgroup.mem_map_of_mem _ hs)]
  have hpos : 0 < (unipReal q).det.val := by rw [det_unipReal]; exact one_pos
  have := congrFun hper z
  rw [slash_apply, σ_of_det_pos hpos, det_unipReal, abs_one, Complex.ofReal_one, _root_.one_zpow,
    mul_one, denom_unipReal, _root_.one_zpow, mul_one, unipReal_smul] at this
  exact this

theorem isZeroAtImInfty_slash (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (δ : GL (Fin 2) ℚ) :
    IsZeroAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    refine ⟨δ • OnePoint.infty, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]
    rfl
  exact f.zero_at_cusps' hc (toReal δ) rfl

theorem integral_archLift_cuspForm_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {δ : GL (Fin 2) ℚ} (hδ : 0 < (δ.det.val : ℚ)) {M : ℕ} (hM : 0 < M)
    (hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N) {h : GL (Fin 2) ℝ}
    (hpos : 0 < h.det.val) :
    ∫ t in (0 : ℝ)..M, archLift k f (toReal δ * (unipReal t * h)) = 0 := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  set F := (f : ℍ → ℂ) ∣[k] toReal δ
  have hδR : 0 < (toReal δ).det.val := by rw [det_toReal]; exact_mod_cast hδ
  have hdne : ((toReal δ).det.val : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hδR.ne')
  set j := denom h ((UpperHalfPlane.I : ℍ) : ℂ)
  set z := h • UpperHalfPlane.I
  set C : ℂ := (((toReal δ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal δ).det.val : ℂ) ^ k *
    ((j / (‖j‖ : ℂ)) ^ (-k) * (Real.sqrt z.im : ℂ) ^ k)
  have key : ∀ t : ℝ, archLift k f (toReal δ * (unipReal t * h)) = C * F (t +ᵥ z) := by
    intro t
    have hy : 0 < (unipReal t * h).det.val := by
      rw [map_mul, Units.val_mul, det_unipReal, one_mul]
      exact hpos
    have h1 := archLift_mul_left (k := k) (f : ℍ → ℂ) hδR hy
    rw [archLift_unipReal_mul F hpos t] at h1
    rw [eq_inv_mul_iff_mul_eq₀ hdne |>.2 h1]
    simp only [C, j, z]
    ring
  have hzero : ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0 := by
    refine integral_vadd_eq_zero (f.holo'.slash k (toReal δ)) (by exact_mod_cast hM)
      (fun z' => ?_) (isZeroAtImInfty_slash f δ) z
    have := slash_periodic hf (M : ℚ) hmem z'
    simpa using this
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, hzero, mul_zero]

theorem toReal_epsilon_mul_unipReal_mul (s : ℝ) :
    toReal epsilon * unipReal s * toReal epsilon = unipReal (-s) := by
  have he : (toReal epsilon : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [epsilon]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, he]
  change (!![-1, 0; 0, 1] * unipMatrix (n := 2) (r := 1) (fun _ => s) * !![-1, 0; 0, 1] :
    Matrix (Fin 2) (Fin 2) ℝ) = unipMatrix (n := 2) (r := 1) (fun _ => -s)
  obtain ⟨u00, u01, u10, u11⟩ := unipMatrix_eval s
  obtain ⟨v00, v01, v10, v11⟩ := unipMatrix_eval (-s)
  rw [Matrix.eta_fin_two (unipMatrix (n := 2) (r := 1) (fun _ => s)),
    Matrix.eta_fin_two (unipMatrix (n := 2) (r := 1) (fun _ => -s)), u00, u01, u10, u11, v00, v01,
    v10, v11]
  simp

variable (N) in

theorem exists_finiteDiagonal_mul_pos (w : FiniteAdelicGL ℚ 2) (h : GL (Fin 2) ℝ) :
    ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N, w = finiteDiagonal ℚ 2 γ * u ∧
      0 < ((toReal γ)⁻¹ * h).det.val := by
  obtain ⟨γ₀, u₀, hu₀, hw⟩ := exists_eq_finiteDiagonal_mul N w
  by_cases hs : 0 < ((toReal γ₀)⁻¹ * h).det.val
  · exact ⟨γ₀, u₀, hu₀, hw, hs⟩
  · refine ⟨γ₀ * epsilon, (finiteDiagonal ℚ 2 epsilon)⁻¹ * u₀,
      mul_mem (inv_mem (finiteDiagonal_epsilon_mem N)) hu₀, ?_, ?_⟩
    · rw [hw, map_mul, mul_assoc, mul_inv_cancel_left]
    · have hneg : ((toReal γ₀)⁻¹ * h).det.val < 0 :=
        lt_of_le_of_ne (not_lt.1 hs) (Units.ne_zero _)
      have e : (toReal (γ₀ * epsilon))⁻¹ * h = (toReal epsilon)⁻¹ * ((toReal γ₀)⁻¹ * h) := by
        rw [map_mul, _root_.mul_inv_rev, mul_assoc]
      rw [e, map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal_epsilon, inv_neg,
        inv_one]
      linarith

theorem finiteDiagonal_conj_mem {w : FiniteAdelicGL ℚ 2} {M : ℕ}
    (hconj : ∀ y ∈ levelIdeal M, w⁻¹ * unipFin y * w ∈ Gamma0Level N) {γ : GL (Fin 2) ℚ}
    {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (hw : w = finiteDiagonal ℚ 2 γ * u) {q : ℚ}
    (hq : algebraMap ℚ 𝔸f q ∈ levelIdeal M) :
    finiteDiagonal ℚ 2 (γ⁻¹ * unipRat q * γ) ∈ Gamma0Level N := by
  have hγ : finiteDiagonal ℚ 2 γ = w * u⁻¹ := by rw [hw, mul_inv_cancel_right]
  have : finiteDiagonal ℚ 2 (γ⁻¹ * unipRat q * γ) =
      u * (w⁻¹ * unipFin (algebraMap ℚ 𝔸f q) * w) * u⁻¹ := by
    rw [map_mul, map_mul, map_inv, finiteDiagonal_unipRat, hγ]
    group
  rw [this]
  exact mul_mem (mul_mem hu (hconj _ hq)) (inv_mem hu)

theorem isCuspidal_liftEquiv_cuspForm (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  set φ : AdelicGL ℚ 2 → ℂ := ↑(liftEquiv N k f.toSlashInvariantForm)
  have hφ : IsWeightLevel N k φ := (liftEquiv N k f.toSlashInvariantForm).2
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  have hφa : ∀ x : GL (Fin 2) ℝ, 0 < x.det.val → φ (realEmb x) = archLift k f x := fun x hx =>
    adelicLift_realEmb hf hx
  set h := realPart g
  set w := (prodEquiv ℚ 2 g).2
  rw [← realEmb_realPart_mul_finEmb g]
  obtain ⟨M, hM, hconj⟩ := exists_level_conj N w
  have : NeZero M := ⟨hM.ne'⟩
  rw [constantTerm_realEmb_mul_finEmb_of_conj hφ h hconj]
  refine smul_eq_zero_of_right _ ?_
  obtain ⟨γ, u, hu, hw, hdet⟩ := exists_finiteDiagonal_mul_pos N w h
  have hdetn : ∀ t : ℝ, ((toReal γ)⁻¹ * (unipReal t * h)).det.val = ((toReal γ)⁻¹ * h).det.val := by
    intro t
    simp only [map_mul, Units.val_mul, det_unipReal, one_mul]
  have hint : ∀ t : ℝ, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) =
      archLift k f ((toReal γ)⁻¹ * (unipReal t * h)) := by
    intro t
    rw [hw, hφ.apply_realEmb_mul_finiteDiagonal γ _ hu]
    exact hφa _ (by rw [hdetn]; exact hdet)
  simp_rw [hint]
  have hMmem : algebraMap ℚ 𝔸f (M : ℚ) ∈ levelIdeal M := ⟨1, one_mem _, by simp⟩
  have hMneg : algebraMap ℚ 𝔸f (-(M : ℚ)) ∈ levelIdeal M := ⟨-1, neg_mem (one_mem _), by simp⟩
  have hsplit : ((toReal γ)⁻¹ * h).det.val = ((γ.det.val : ℚ) : ℝ)⁻¹ * h.det.val := by
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal]
  rcases lt_or_gt_of_ne (Units.ne_zero γ.det) with hneg | hpos
  ·
    have hh : h.det.val < 0 := by
      rw [hsplit] at hdet
      have : ((γ.det.val : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
      have : ((γ.det.val : ℚ) : ℝ)⁻¹ < 0 := inv_lt_zero.2 this
      nlinarith
    set δ := γ⁻¹ * epsilon
    have hδ : 0 < (δ.det.val : ℚ) := by
      simp only [δ, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      have hε : (epsilon.det.val : ℚ) = -1 := by
        have := det_toReal_epsilon
        rw [det_toReal] at this
        exact_mod_cast this
      rw [hε]
      have : (γ.det.val : ℚ)⁻¹ < 0 := inv_lt_zero.2 hneg
      linarith
    set h' := toReal epsilon * h
    have hh' : 0 < (unipReal (-(M : ℝ)) * h').det.val := by
      simp only [h', map_mul, Units.val_mul, det_unipReal, det_toReal_epsilon, one_mul]
      linarith
    have hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N := by
      have : δ * unipRat M * δ⁻¹ = γ⁻¹ * unipRat (-(M : ℚ)) * γ := by
        simp only [δ, _root_.mul_inv_rev, inv_inv, epsilon_inv]
        rw [← epsilon_mul_unipRat_mul_epsilon]
        group
      rw [this]
      exact finiteDiagonal_conj_mem hconj hu hw hMneg
    have hrew : ∀ t : ℝ, archLift k f ((toReal γ)⁻¹ * (unipReal t * h)) =
        archLift k f (toReal δ * (unipReal (-t) * h')) := by
      intro t
      congr 1
      simp only [δ, h', map_mul, map_inv]
      have e := toReal_epsilon_mul_unipReal_mul (-t)
      rw [neg_neg] at e
      rw [← e]
      group
    simp_rw [hrew]
    rw [intervalIntegral.integral_comp_neg (fun s => archLift k f (toReal δ * (unipReal s * h'))),
      neg_zero]
    have hshift := intervalIntegral.integral_comp_sub_right
      (fun s => archLift k f (toReal δ * (unipReal s * h'))) (M : ℝ) (a := 0) (b := M)
    simp only [zero_sub, sub_self] at hshift
    rw [← hshift]
    have hsub : ∀ s : ℝ, archLift k f (toReal δ * (unipReal (s - M) * h')) =
        archLift k f (toReal δ * (unipReal s * (unipReal (-(M : ℝ)) * h'))) := by
      intro s
      rw [sub_eq_add_neg, unipReal_add, mul_assoc]
    simp_rw [hsub]
    exact integral_archLift_cuspForm_eq_zero f hδ hM hmem hh'
  ·
    have hh : 0 < h.det.val := by
      rw [hsplit] at hdet
      have : (0 : ℝ) < ((γ.det.val : ℚ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hpos)
      exact pos_of_mul_pos_right hdet this.le
    have hδ : 0 < ((γ⁻¹).det.val : ℚ) := by
      rw [map_inv, Units.val_inv_eq_inv_val]
      exact inv_pos.2 hpos
    have hmem : finiteDiagonal ℚ 2 (γ⁻¹ * unipRat M * γ⁻¹⁻¹) ∈ Gamma0Level N := by
      rw [inv_inv]
      exact finiteDiagonal_conj_mem hconj hu hw hMmem
    have := integral_archLift_cuspForm_eq_zero f hδ hM hmem hh
    rwa [map_inv] at this

end GL2Classical

end

end GroundTheory.Automorphic
