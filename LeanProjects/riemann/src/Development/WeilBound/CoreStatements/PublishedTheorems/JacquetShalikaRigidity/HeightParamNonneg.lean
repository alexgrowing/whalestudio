import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.AutomorphicForms.ReductionMahler
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData
namespace height_param_nonneg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem height_pos' (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) : 0 < height g ξ := by
  obtain ⟨ε, hε, h⟩ := exists_pos_le_height (isCompact_singleton (x := g))
  exact hε.trans_le (h g rfl ξ hξ)

theorem invT_mul (g h : GA E k) : invT (g * h) = invT g * invT h := by
  ext i j
  simp [invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem invT_invT (g : GA E k) : invT (invT g) = g := by
  ext i j
  rfl

theorem dt_pos_of (hD : D0) (g : GA E k) : 0 < Dt g := (hD E k).1 g

end height_param_nonneg

namespace height_param_nonneg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem dt_mul (hD : D0) (g h : GA E k) : Dt (g * h) = Dt g * Dt h := (hD E k).2.1 g h

theorem c2 (hD : D0) (γ : GL (Fin k) E) (g : GA E k) (ξ : Fin k → E) :
    ht (ratGL E k γ * g) ξ = ht g (ξ ᵥ* γ.val) := by
  unfold ht
  rw [dt_mul hD, (hD E k).2.2.2.1 γ, one_mul]
  congr 1
  exact height_diagonal_mul γ g ξ

theorem dt_scalar (c : GroundTheory.Global.IdeleGroup E) :
    Dt (GeneralLinearGroup.scalar (Fin k) c : GA E k) = (GroundTheory.Global.IdeleGroup.ideleModule E c : ℝ) ^ k := by
  have e : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin k) c : GA E k) = c ^ k := by
    ext
    simp [Matrix.det_diagonal]
  unfold Dt
  rw [e, map_pow, Positive.val_pow]

theorem height_scalar_mul (c : GroundTheory.Global.IdeleGroup E) (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    Reduction.height ((GeneralLinearGroup.scalar (Fin k) c : GA E k) * g) ξ =
      (GroundTheory.Global.IdeleGroup.ideleModule E c : ℝ) * Reduction.height g ξ := by
  have e : ratVec ξ ᵥ* (((GeneralLinearGroup.scalar (Fin k) c : GA E k) * g : GA E k) : Matrix (Fin k) (Fin k) (Ad E)) =
      (c : Ad E) • (ratVec ξ ᵥ* (g : Matrix (Fin k) (Fin k) (Ad E))) := by
    rw [Units.val_mul, ← vecMul_vecMul, ← smul_vecMul]
    congr 1
    ext i
    simp [Matrix.vecMul_diagonal, mul_comm]
  unfold Reduction.height
  rw [e]
  exact adelicNorm_smul (hasFiniteContent_height g hξ) c

theorem c3 (hD : D0) (t : ℝ) (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    ht (splitCentre E k t * g) ξ = ht g ξ := by
  have hk : k ≠ 0 := by
    rintro rfl
    exact hξ (Subsingleton.elim _ _)
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  set c := infId E (expU fun _ : InfinitePlace E => (t : ℂ))
  have hM : 0 < (GroundTheory.Global.IdeleGroup.ideleModule E c : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule E c).2
  unfold ht
  rw [height_scalar_mul c g hξ, dt_mul hD, dt_scalar,
    Real.mul_rpow (pow_nonneg hM.le _) ((hD E k).1 g).le, Real.pow_rpow_inv_natCast hM.le hk]
  exact mul_div_mul_left _ _ hM.ne'

theorem c4 (hD : D0) (C : Set (GA E k)) (hC : IsCompact C) :
    ∃ B : ℝ, ∀ c ∈ C, ∀ (g : GA E k) ξ, ξ ≠ 0 → ht (g * c) ξ ≤ B * ht g ξ := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun c hc => hc.elim⟩
  obtain ⟨P, hP, hPC⟩ := exists_adelicNorm_vecMul_le_mul hC
  obtain ⟨c₀, -, hc₀⟩ := hC.exists_isMinOn hne (hD E k).2.2.1.continuousOn
  set m := Dt c₀
  have hm : 0 < m := (hD E k).1 c₀
  refine ⟨P / m ^ ((k : ℝ)⁻¹), fun c hc g ξ hξ => ?_⟩
  have hg := (hD E k).1 g
  have hH : Reduction.height (g * c) ξ ≤ P * Reduction.height g ξ := by
    unfold Reduction.height
    rw [Units.val_mul, ← vecMul_vecMul]
    exact hPC c hc _ (hasFiniteContent_height g hξ)
  have hmc : m ≤ Dt c := hc₀ hc
  have hr : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg k)
  have hden : m ^ ((k : ℝ)⁻¹) * Dt g ^ ((k : ℝ)⁻¹) ≤ Dt (g * c) ^ ((k : ℝ)⁻¹) := by
    rw [dt_mul hD, ← Real.mul_rpow hm.le hg.le, mul_comm (Dt g)]
    exact Real.rpow_le_rpow (mul_nonneg hm.le hg.le) (mul_le_mul_of_nonneg_right hmc hg.le) hr
  have h1 : 0 < m ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hm _
  have h2 : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hg _
  unfold ht
  calc Reduction.height (g * c) ξ / Dt (g * c) ^ ((k : ℝ)⁻¹)
      ≤ P * Reduction.height g ξ / (m ^ ((k : ℝ)⁻¹) * Dt g ^ ((k : ℝ)⁻¹)) :=
        div_le_div₀ (mul_nonneg hP.le (height_nonneg g ξ)) hH (mul_pos h1 h2) hden
    _ = P / m ^ ((k : ℝ)⁻¹) * (Reduction.height g ξ / Dt g ^ ((k : ℝ)⁻¹)) := by
        field_simp

end height_param_nonneg
namespace height_param_nonneg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem isOpen_vecInt (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {y : Fin k → Ad E | ∀ v, v ∉ S → ∀ i, (y i).2 v ∈ v.adicCompletionIntegers E} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_integer _) (p := fun v => v ∉ S)
  have e : {y : Fin k → Ad E | ∀ v, v ∉ S → ∀ i, (y i).2 v ∈ v.adicCompletionIntegers E} =
      ⋂ i, (fun y : Fin k → Ad E => (y i).2) ⁻¹' {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers E} := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => h.preimage (continuous_snd.comp (continuous_apply i))

omit [IsTotallyComplex E] in
theorem exists_finite_vecInt {C : Set (Fin k → Ad E)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ y ∈ C, ∀ v, v ∉ S → ∀ i, (y i).2 v ∈ v.adicCompletionIntegers E := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 E)) =>
      {y : Fin k → Ad E | ∀ v, v ∉ S → ∀ i, (y i).2 v ∈ v.adicCompletionIntegers E})
    (fun S => isOpen_vecInt S) (fun y _ => by
      have hfin : (⋃ i, {v : HeightOneSpectrum (𝓞 E) | (y i).2 v ∉ v.adicCompletionIntegers E}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (y i).2.2
      refine Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv i => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, h⟩)))
  refine ⟨T.sup id, fun y hy v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

omit [IsTotallyComplex E] in
theorem norm_finComp_le_one {y : Fin k → Ad E} {v : HeightOneSpectrum (𝓞 E)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers E) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => norm_le_one_of_mem v (h i)

omit [IsTotallyComplex E] in
theorem c5 (C : Set (Fin k → Ad E)) (hC : IsCompact C) : ∃ B : ℝ, ∀ (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val ∈ C → height g ξ ≤ B := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_vecInt hC
  have hinf : ∀ w : InfinitePlace E, ∃ m : ℝ, 1 ≤ m ∧ ∀ y ∈ C, euclidNorm (infComp w y) ≤ m := fun w =>
    exists_one_le_bound hC (f := fun y => euclidNorm (infComp w y))
      (continuous_euclidNorm.comp (continuous_pi fun i =>
        (continuous_apply w).comp (continuous_fst.comp (continuous_apply i))))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℝ, 1 ≤ m ∧ ∀ y ∈ C, ‖finComp v y‖ ≤ m := fun v =>
    exists_one_le_bound hC (f := fun y => ‖finComp v y‖)
      (continuous_norm.comp (continuous_pi fun i =>
        (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))))
  choose a ha1 ha using hinf
  choose b hb1 hb using hfin
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, fun g ξ hξ hy => ?_⟩
  have hfc := hasFiniteContent_height g hξ
  set y : Fin k → Ad E := (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val with hy'
  have e : height g ξ = adelicNorm y := rfl
  rw [e, adelicNorm]
  set b' : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  have hfp : ∏ᶠ v, ‖finComp v y‖ ≤ ∏ v ∈ S, b v := by
    have hsub : Function.mulSupport b' ⊆ (S : Set _) := fun v hv => by
      by_contra h
      exact hv (by simp only [hb', if_neg (show v ∉ S from h)])
    refine (finprod_le_finprod_of_nonneg hfc.finite_mulSupport ((S.finite_toSet).subset hsub)
      (fun v => norm_nonneg _) fun v => ?_).trans (le_of_eq ?_)
    · simp only [hb']
      split_ifs with hv
      · exact hb v y hy
      · exact norm_finComp_le_one (hS y hy v hv)
    · rw [finprod_eq_prod_of_mulSupport_subset b' hsub]
      exact Finset.prod_congr rfl fun v hv => by simp only [hb', if_pos hv]
  refine mul_le_mul (Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
    fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _) hfp
    (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (ha1 w)) _)

end height_param_nonneg
namespace height_param_nonneg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem norm_pInf_eq (a : Ad E) (w : InfinitePlace E) : ‖pInf E a w‖ = ‖a.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem pInf_infGL_entry (x : GL (Fin k) (Cinf E)) (i j : Fin k) :
    pInf E ((infGL E k x : GA E k) i j) = x i j :=
  congrArg (fun y : GL (Fin k) (Cinf E) => y i j) (pInf_infGL (E := E) x)

theorem pFin_infGL_entry (x : GL (Fin k) (Cinf E)) (i j : Fin k) :
    pFin E ((infGL E k x : GA E k) i j) = (1 : GL (Fin k) (Af E)) i j :=
  congrArg (fun y : GL (Fin k) (Af E) => y i j) (pFin_infGL (E := E) x)

theorem finAt_infGL_eq_one (x : GL (Fin k) (Cinf E)) (v : HeightOneSpectrum (𝓞 E)) :
    finAt v (infGL E k x : AdelicGLn.AdelicGL E k) = 1 := by
  ext i j
  rw [finAt_apply]
  have := congrArg (fun z : Af E => z v) (pFin_infGL_entry x i j)
  simp only [Units.val_one, Matrix.one_apply] at this ⊢
  split_ifs at this ⊢ <;> exact congrArg HeightOneSpectrum.adicCompletion.toCompletion this

theorem height_le_infGL_mul (g : GA E k) (x : GL (Fin k) (Cinf E)) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    height g ξ ≤ (∏ w : InfinitePlace E,
      (√k * (k * ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖)) ^ w.mult) *
        height (g * infGL E k x) ξ := by
  have hg : g = (g * infGL E k x) * infGL E k x⁻¹ := by
    rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have key : height g ξ = adelicNorm ((ratVec ξ ᵥ* ((g * infGL E k x : GA E k) : Matrix (Fin k) (Fin k) (Ad E))) ᵥ*
      ((infGL E k x⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E))) := by
    conv_lhs => rw [hg]
    rw [Reduction.height, Units.val_mul, ← vecMul_vecMul]
  have hy' := hasFiniteContent_height (g * infGL E k x) hξ
  rw [key]
  have := adelicNorm_le_of_local (hy'.vecMul (infGL E k x⁻¹)) hy'
    (fun _ => √k * (k * ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖)) (fun _ => 1) ∅
    (fun w => ?_) (fun _ _ => rfl) (fun v => ?_)
  · simpa [Reduction.height] using this
  · rw [infComp_vecMul_GL]
    refine euclidNorm_vecMul_le (norm_nonneg _) (fun i j => ?_) _
    rw [infAt_apply, ← norm_pInf_eq, pInf_infGL_entry]
    exact (norm_le_pi_norm ((Matrix.of.symm x⁻¹.val) i j) w).trans
      ((norm_le_pi_norm ((Matrix.of.symm x⁻¹.val) i) j).trans (norm_le_pi_norm (Matrix.of.symm x⁻¹.val) i))
  · rw [finComp_vecMul_GL, finAt_infGL_eq_one, Units.val_one, vecMul_one, one_mul]

theorem dt_infGL_prod (x : GL (Fin k) (Cinf E)) :
    Dt (infGL E k x) = ∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det x : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult := by
  rw [Dt, det_infGL, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ z, pInf E (sInf E z) = z := fun z => (infEq E).symm_apply_apply z
  have h2 : ∀ z, pFin E (sInf E z) = 0 := fun _ => rfl
  set u := GeneralLinearGroup.det x
  have hI : pInf E ((infId E u : (Ad E)ˣ) : Ad E) = u := by
    change pInf E (1 - sInf E 1 + sInf E u) = u
    rw [map_add, map_sub, map_one, h1, h1]; simp
  have hF : pFin E ((infId E u : (Ad E)ˣ) : Ad E) = 1 := by
    change pFin E (1 - sInf E 1 + sInf E u) = 1
    rw [map_add, map_sub, map_one, h2, h2]; simp
  have e2 : ∀ v : HeightOneSpectrum (𝓞 E), ‖((infId E u : (Ad E)ˣ) : Ad E).2 v‖ = 1 := fun v => by
    change ‖(pFin E ((infId E u : (Ad E)ˣ) : Ad E)) v‖ = 1
    rw [hF]; simp
  rw [finprod_congr e2, finprod_one, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← norm_pInf_eq, hI]

theorem det_norm_le_factorial (x : GL (Fin k) (Cinf E)) (w : InfinitePlace E) :
    ‖((GeneralLinearGroup.det x : (Cinf E)ˣ) : Cinf E) w‖ ≤
      k.factorial * ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ ^ k := by
  have e : ((GeneralLinearGroup.det x : (Cinf E)ˣ) : Cinf E) w =
      ((x : Matrix (Fin k) (Fin k) (Cinf E)).map (Pi.evalRingHom _ w)).det := by
    rw [GeneralLinearGroup.val_det_apply]
    exact RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (x : Matrix (Fin k) (Fin k) (Cinf E))
  rw [e]
  have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ)
    (A := (x : Matrix (Fin k) (Fin k) (Cinf E)).map (Pi.evalRingHom _ w))
    (x := ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖) (fun i j => ?_)
  · simp only [nsmul_eq_mul, Fintype.card_fin] at this
    exact this
  · show ‖x i j w‖ ≤ _
    exact (norm_le_pi_norm ((Matrix.of.symm x.val) i j) w).trans
      ((norm_le_pi_norm ((Matrix.of.symm x.val) i) j).trans (norm_le_pi_norm (Matrix.of.symm x.val) i))

omit [NumberField E] [IsTotallyComplex E] in
theorem rpow_inv_le_one_add (y : ℝ) (hy : 0 ≤ y) (k : ℕ) : y ^ ((k : ℝ)⁻¹) ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_le_one hy h (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹); linarith
  · have hr : (k : ℝ)⁻¹ ≤ 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
    have := Real.rpow_le_rpow_of_exponent_le h hr
    rw [Real.rpow_one] at this; linarith

theorem infinite_place_prod_le (L T : ℝ) (hL : 0 ≤ L) (hLT : L ≤ T) :
    (∏ w : InfinitePlace E, (√k * (k * L)) ^ w.mult) ≤
      (√k * k) ^ (2 * Fintype.card (InfinitePlace E)) * T ^ (2 * Fintype.card (InfinitePlace E)) := by
  have e : (∏ w : InfinitePlace E, (√k * (k * L)) ^ w.mult) = ((√k * (k * L)) ^ 2) ^ Fintype.card (InfinitePlace E) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun w _ => by rw [IsTotallyComplex.mult_eq]
  rw [e]
  generalize Fintype.card (InfinitePlace E) = d
  rw [← mul_pow, ← pow_mul, ← mul_assoc]
  gcongr

theorem dt_infGL_le (x : GL (Fin k) (Cinf E)) (T : ℝ) (hT : ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ ≤ T) :
    Dt (infGL E k x) ≤ (k.factorial : ℝ) ^ (2 * Fintype.card (InfinitePlace E)) *
      T ^ (k * (2 * Fintype.card (InfinitePlace E))) := by
  rw [dt_infGL_prod]
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  have e : (∏ _w : InfinitePlace E, ((k.factorial : ℝ) * T ^ k) ^ 2) =
      (((k.factorial : ℝ) * T ^ k) ^ 2) ^ Fintype.card (InfinitePlace E) := by
    rw [Finset.prod_const, Finset.card_univ]
  have h1 : (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det x : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) ≤
      ∏ _w : InfinitePlace E, ((k.factorial : ℝ) * T ^ k) ^ 2 := by
    refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
    rw [IsTotallyComplex.mult_eq]
    refine pow_le_pow_left₀ (norm_nonneg _) ((det_norm_le_factorial x w).trans ?_) 2
    gcongr
  refine h1.trans (le_of_eq ?_)
  rw [e]
  generalize Fintype.card (InfinitePlace E) = d
  rw [← pow_mul, mul_pow, ← pow_mul]

omit [NumberField E] [IsTotallyComplex E] in
theorem height_product_arith {H H' P Dx Dxr A F Ta Tb : ℝ} (hH : H ≤ P * H') (hP : P ≤ A * Ta) (hH0 : 0 ≤ H')
    (hDxr0 : 0 ≤ Dxr) (hDxr : Dxr ≤ 1 + Dx) (hDx : Dx ≤ F * Tb) (hA : 0 ≤ A) (hTa : 0 ≤ Ta) (hF : 0 ≤ F)
    (hTb : 1 ≤ Tb) : H * Dxr ≤ A * (1 + F) * (Ta * Tb) * H' := by
  have h3 : 0 ≤ A * Ta * H' := mul_nonneg (mul_nonneg hA hTa) hH0
  calc H * Dxr ≤ (P * H') * Dxr := mul_le_mul_of_nonneg_right hH hDxr0
    _ ≤ (A * Ta * H') * (1 + Dx) := mul_le_mul (mul_le_mul_of_nonneg_right hP hH0) hDxr hDxr0 h3
    _ ≤ (A * Ta * H') * ((1 + F) * Tb) := by
        refine mul_le_mul_of_nonneg_left ?_ h3
        nlinarith
    _ = A * (1 + F) * (Ta * Tb) * H' := by ring

theorem c6 (hD : D0) : ∃ (B : ℝ) (N : ℕ), 0 ≤ B ∧ ∀ (x : GL (Fin k) (Cinf E)) (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    ht g ξ ≤ B * (1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N * ht (g * infGL E k x) ξ := by
  obtain ⟨hpos, hmul, -⟩ := hD E k
  refine ⟨(√k * k) ^ (2 * Fintype.card (InfinitePlace E)) * (1 + (k.factorial : ℝ) ^ (2 * Fintype.card (InfinitePlace E))),
    2 * Fintype.card (InfinitePlace E) + k * (2 * Fintype.card (InfinitePlace E)), by positivity, fun x g ξ hξ => ?_⟩
  have hLx : 0 ≤ ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ := norm_nonneg _
  have hL : 0 ≤ ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖ := norm_nonneg _
  have hP := infinite_place_prod_le (E := E) (k := k) _ (1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖) hL (by linarith)
  have hDx := dt_infGL_le x (1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖) (by linarith)
  have hH := height_le_infGL_mul g x hξ
  have hH0 : 0 ≤ Reduction.height (g * infGL E k x) ξ := height_nonneg _ _
  have hDg := hpos g
  have hDx0 := hpos (infGL E k x)
  have hDgr : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDg _
  have hDxr : 0 < Dt (infGL E k x) ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDx0 _
  have hR := rpow_inv_le_one_add _ hDx0.le k
  have hT1 : 1 ≤ 1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖ := by linarith
  unfold ht
  rw [hmul, Real.mul_rpow hDg.le hDx0.le]
  generalize 1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖ = T at hP hDx hT1 ⊢
  generalize Fintype.card (InfinitePlace E) = d at hP hDx ⊢
  generalize (∏ w : InfinitePlace E, (√k * (k * ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖)) ^ w.mult) = P
    at hP hH
  generalize Reduction.height (g * infGL E k x) ξ = H' at hH hH0 ⊢
  generalize Reduction.height g ξ = H at hH ⊢
  generalize Dt (infGL E k x) ^ ((k : ℝ)⁻¹) = Dxr at hDxr hR ⊢
  generalize Dt (infGL E k x) = Dx at hR hDx
  generalize Dt g ^ ((k : ℝ)⁻¹) = Dgr at hDgr ⊢
  have hT0 : 0 ≤ T := by linarith
  have key := height_product_arith hH hP hH0 hDxr.le hR hDx (by positivity) (by positivity)
    (by positivity) (one_le_pow₀ hT1)
  rw [← pow_add] at key
  rw [div_le_iff₀ hDgr, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (mul_pos hDgr hDxr)]
  calc H * (Dgr * Dxr) = (H * Dxr) * Dgr := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right key hDgr.le

end height_param_nonneg

theorem height_change_of_D0 : D0 → H0 := by
  intro hD E _ _ _ k
  refine ⟨fun g ξ hξ => ?_, fun γ g ξ => height_param_nonneg.c2 hD γ g ξ, fun t g ξ hξ => height_param_nonneg.c3 hD t g hξ,
    fun C hC => height_param_nonneg.c4 hD C hC, fun C hC => height_param_nonneg.c5 C hC, height_param_nonneg.c6 hD,
    fun g h => ⟨height_param_nonneg.invT_mul g h, height_param_nonneg.invT_invT g⟩⟩
  unfold ht
  exact div_pos (height_param_nonneg.height_pos' g hξ) (Real.rpow_pos_of_pos ((hD E k).1 g) _)

end PositivityTheory.AdelicQuotientData

end
