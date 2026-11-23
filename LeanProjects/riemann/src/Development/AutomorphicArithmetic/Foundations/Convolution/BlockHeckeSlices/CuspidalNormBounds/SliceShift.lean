import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatCons
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslate
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

private def aV (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (v : ℝ) : GA E (r + s) :=
  lev (Ad E) r s (zt E r v, 1)

private theorem zt_add (a b : ℝ) : zt E r (a + b) = zt E r a * zt E r b := by
  unfold zt
  rw [← map_mul]
  exact congrArg _ (Subtype.ext (Real.exp_add a b))

private theorem zt_zero : zt E r 0 = 1 := by
  unfold zt
  rw [show (⟨Real.exp 0, Real.exp_pos 0⟩ : {x : ℝ // 0 < x}) = 1 from Subtype.ext Real.exp_zero, map_one]

private theorem zt_comm (v : ℝ) (g : GA E r) : zt E r v * g = g * zt E r v :=
  centralSection_mul_comm _ g

private theorem aV_zero : aV E r s 0 = 1 := by
  rw [aV, zt_zero]
  exact map_one _

private theorem ct_rt {n : ℕ} (h g : GA E n) (φ : Sm E n) :
    AutomorphicForm.constantTerm r (rt E n h φ).1 g = AutomorphicForm.constantTerm r φ.1 (g * h) := by
  unfold AutomorphicForm.constantTerm
  refine integral_congr_ae (.of_forall fun X => ?_)
  show φ.1 (_ * g * h) = φ.1 (_ * (g * h))
  rw [mul_assoc]

private theorem shift (f : GA E r → ℂ) (t v : ℝ) (φ : Sm E (r + s)) (m : GA E s) :
    slice f t (rt E (r + s) (aV E r s v) φ).1 m = slice f (t + v) φ.1 m := by
  unfold slice
  refine integral_congr_ae (.of_forall fun y => ?_)
  show AutomorphicForm.constantTerm r (rt E (r + s) (aV E r s v) φ).1 _ * _ = AutomorphicForm.constantTerm r φ.1 _ * _
  rw [ct_rt, aV, ← map_mul]
  congr 3
  refine Prod.ext ?_ (mul_one _)
  show zt E r t * _ * zt E r v = zt E r (t + v) * _
  rw [zt_add, mul_assoc, mul_assoc, ← zt_comm v]

private theorem zt_eq (t : ℝ) :
    zt E r t = GlobalTheory.UnitaryBC.splitCentre E r (t * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r
    (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)
  rw [Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t] at h
  exact h

private theorem aV_eq (v : ℝ) :
    aV E r s v = PositivityTheory.Rg.Rs.aT E (r + s) r (v * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  rw [aV, zt_eq, PositivityTheory.Rg.Rs.SliceClasses.splitCentre_eq_aT, PositivityTheory.Rg.Rs.SliceClasses.lev_aT_left r s r le_rfl]

private theorem hasDeriv_aV (F : Sm E (r + s)) (g : GA E (r + s)) (v : ℝ) :
    HasDerivAt (fun x => F.1 (g * aV E r s x)) ((j1 E r s F).1 (g * aV E r s v)) v := by
  set c : ℝ := ((r * Module.finrank ℚ E : ℝ))⁻¹ with hc
  have h := GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right E r s F g (v * c)
  have h2 := h.scomp v ((hasDerivAt_id v).mul_const c)
  simp only [Function.comp_def, id, one_mul] at h2
  have ej : ∀ y, (j1 E r s F).1 y =
      c • ((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 y := fun y => by
    show (((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹) * _ = _
    rw [Complex.real_smul, hc, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Nat.cast_mul]
  simp only [aV_eq, ← hc]
  rw [ej]
  exact h2

private theorem lev_diag {R : Type} [CommRing R] (x : Fin (r + s) → Rˣ) :
    diagUnits (r + s) x = lev R r s (diagUnits r fun i => x (Fin.castAdd s i), diagUnits s fun i => x (Fin.natAdd r i)) := by
  refine Units.ext ?_
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [GlobalTheory.SmGL.stdSum, Matrix.diagonal_apply, Fin.ext_iff] <;> omega

private theorem posIdele_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

private theorem height_aV (hr : 0 < r) : ∃ H : ℝ, 0 ≤ H ∧ ∀ v : ℝ, |v| ≤ 1 → AutomorphicForm.height (aV E r s v) ≤ H := by
  set c : ℝ := ((r * Module.finrank ℚ E : ℝ))⁻¹ with hc
  have c0 : 0 ≤ c := by positivity
  refine ⟨Real.exp c ^ (2 * Fintype.card (InfinitePlace E)), by positivity, fun v hv => ?_⟩
  set ρ : Fin (r + s) → ℝ := fun i => if (i : ℕ) < r then Real.exp (v * c) else 1 with hρd
  have hρ : ∀ i, 0 < ρ i := fun i => by
    simp only [hρd]
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  have e : aV E r s v = diagUnits (r + s) fun i => posIdele (K := E) (ρ i) (hρ i) := by
    rw [lev_diag, aV]
    refine congrArg _ (Prod.ext ?_ ?_)
    · refine congrArg (diagUnits r) (funext fun i => ?_)
      refine posIdele_eq (Real.rpow_pos_of_pos (Real.exp_pos _) _) _ ?_
      simp only [hρd, Fin.val_castAdd, i.2, if_true]
      rw [← Real.exp_mul]
    · symm
      refine Units.ext (Matrix.ext fun i j => ?_)
      have e1 : posIdele (K := E) (ρ (Fin.natAdd r i)) (hρ _) = 1 := by
        rw [← PositivityTheory.Rg.Rs.SliceClasses.A_posIdele_one]
        refine posIdele_eq _ _ ?_
        simp [hρd]
      simp [coe_diagUnits, e1, Matrix.one_apply, Matrix.diagonal_apply]
  rw [e]
  refine GroundTheory.Automorphic.CuspidalSpectrum.height_diagUnits_posIdele_le hρ (Real.one_le_exp c0) fun i => ?_
  have b1 : |v * c| ≤ c := by
    rw [abs_mul, abs_of_nonneg c0]
    exact mul_le_of_le_one_left c0 hv
  simp only [hρd]
  split_ifs
  · rw [← Real.exp_neg]
    exact ⟨Real.exp_le_exp.2 (abs_le.1 b1).2, Real.exp_le_exp.2 (by linarith [(abs_le.1 b1).1])⟩
  · simpa using Real.one_le_exp c0

private theorem taylor (F : Sm E (r + s)) (g : GA E (r + s)) {K : ℝ}
    (hK : ∀ x : ℝ, |x| ≤ 1 → ‖(j1 E r s (j1 E r s F)).1 (g * aV E r s x)‖ ≤ K) {v : ℝ} (hv : |v| ≤ 1) :
    ‖F.1 (g * aV E r s v) - F.1 g - (v : ℂ) * (j1 E r s F).1 g‖ ≤ K * v ^ 2 := by
  have K0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp))
  have hq : ∀ x : ℝ, |x| ≤ 1 → ‖(j1 E r s F).1 (g * aV E r s x) - (j1 E r s F).1 g‖ ≤ K * |x| := by
    intro x hx
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc (-1 : ℝ) 1) (C := K) (x := 0) (y := x)
      (f := fun x : ℝ => (j1 E r s F).1 (g * aV E r s x)) (f' := fun x => (j1 E r s (j1 E r s F)).1 (g * aV E r s x))
      (fun x _ => (hasDeriv_aV (j1 E r s F) g x).hasDerivWithinAt)
      (fun x hx => hK x (abs_le.2 hx)) (convex_Icc _ _) (by simp) (abs_le.1 hx)
    simpa [aV_zero] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc (-|v|) |v|) (C := K * |v|) (x := 0) (y := v)
    (f := fun x : ℝ => F.1 (g * aV E r s x) - (x : ℂ) * (j1 E r s F).1 g)
    (f' := fun x => (j1 E r s F).1 (g * aV E r s x) - (j1 E r s F).1 g)
    (fun x _ => by
      have h1 := hasDeriv_aV F g x
      have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * (j1 E r s F).1 g) ((j1 E r s F).1 g) x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const ((j1 E r s F).1 g)
      exact (h1.sub h2).hasDerivWithinAt)
    (fun x hx => (hq x ((abs_le.2 hx).trans hv)).trans (mul_le_mul_of_nonneg_left (abs_le.2 hx) K0))
    (convex_Icc _ _) (by simp) (by simp [neg_abs_le, le_abs_self])
  simp only [aV_zero, mul_one, Complex.ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at h
  rw [← sq_abs v]
  calc _ = ‖F.1 (g * aV E r s v) - (v : ℂ) * (j1 E r s F).1 g - F.1 g‖ := by congr 1; ring
    _ ≤ K * |v| * |v| := h
    _ = K * |v| ^ 2 := by ring

private theorem exists_casimir_center : ∃ u : UC E (r + s), j1 E r s = uC E (r + s) u :=
  ⟨((r * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i : Fin r, genC τ (Fin.castAdd s i) (Fin.castAdd s i), by
    simp only [j1, map_smul, map_sum, uC_genC]⟩

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.sliceShift :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceShift E := by
  intro E _ _ _ S r s b t φ m hφ
  have hsh : ∀ v, slice b.f.1 t (rt E (r + s) (aV E r s v) φ).1 m = slice b.f.1 (t + v) φ.1 m :=
    fun v => shift _ t v φ m
  refine ⟨hsh, ?_⟩
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨u, hu⟩ := exists_casimir_center (E := E) (r := r) (s := s)
  obtain ⟨B, hB⟩ := hN (u * u)
  obtain ⟨H, H0, hH⟩ := height_aV (E := E) (s := s) b.pos
  obtain ⟨C, R, hCR⟩ := (sliceBound E S r s b).1 N
  have hc1 := AutomorphicForm.one_le_heightConst (K := E) (n := r + s)
  set c0 : ℝ := |B| * (AutomorphicForm.heightConst E (r + s) * H) ^ N with hc0
  have hK : ∀ (g : GA E (r + s)) (x : ℝ), |x| ≤ 1 →
      ‖(j1 E r s (j1 E r s φ)).1 (g * aV E r s x)‖ ≤ c0 * AutomorphicForm.height g ^ N := by
    intro g x hx
    have h1 := hB (g * aV E r s x)
    rw [map_mul, Module.End.mul_apply, ← hu] at h1
    refine h1.trans ?_
    rw [hc0, mul_assoc, ← mul_pow]
    refine mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ?_ N)
      (pow_nonneg (AutomorphicForm.height_pos _).le N) (abs_nonneg _)
    refine (AutomorphicForm.height_mul_le _ _).trans ?_
    have hg := (AutomorphicForm.height_pos g).le
    calc _ ≤ AutomorphicForm.heightConst E (r + s) * AutomorphicForm.height g * H :=
          mul_le_mul_of_nonneg_left (hH x hx) (by positivity)
      _ = _ := by ring
  have hj := Umg.j1 hφ
  have hU : ∀ v : ℝ, Umg ((-1 : ℂ) • φ + (-(v : ℂ)) • j1 E r s φ) := fun v => (hφ.smul _).add (hj.smul _)
  have hexp : ∀ v : ℝ, slice b.f.1 (t + v) φ.1 m - slice b.f.1 t φ.1 m - (v : ℂ) * slice b.f.1 t (j1 E r s φ).1 m =
      slice b.f.1 t (rt E (r + s) (aV E r s v) φ + ((-1 : ℂ) • φ + (-(v : ℂ)) • j1 E r s φ)).1 m := by
    intro v
    have h1 := congrFun (slice_add b t (hφ.tr (aV E r s v)) (hU v)) m
    have h2 := congrFun (slice_add b t (hφ.smul (-1 : ℂ)) (hj.smul (-(v : ℂ)))) m
    have h3 := congrFun (slice_smul b t (-1 : ℂ) hφ) m
    have h4 := congrFun (slice_smul b t (-(v : ℂ)) hj) m
    rw [h1]
    simp only [Pi.add_apply] at *
    rw [h2, h3, h4, hsh]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hbig : ∀ v : ℝ, |v| ≤ 1 → ‖slice b.f.1 (t + v) φ.1 m - slice b.f.1 t φ.1 m -
      (v : ℂ) * slice b.f.1 t (j1 E r s φ).1 m‖ ≤
        (|C| * c0 * Real.exp (R * |t|) * AutomorphicForm.height m ^ N) * |v ^ 2| := by
    intro v hv
    rw [hexp]
    have hb : ∀ g, ‖(rt E (r + s) (aV E r s v) φ + ((-1 : ℂ) • φ + (-(v : ℂ)) • j1 E r s φ)).1 g‖ ≤
        (c0 * v ^ 2) * AutomorphicForm.height g ^ N := by
      intro g
      have h := taylor φ g (hK g) hv
      have e : (rt E (r + s) (aV E r s v) φ + ((-1 : ℂ) • φ + (-(v : ℂ)) • j1 E r s φ)).1 g =
          φ.1 (g * aV E r s v) - φ.1 g - (v : ℂ) * (j1 E r s φ).1 g := by
        show φ.1 (g * aV E r s v) + ((-1 : ℂ) * φ.1 g + (-(v : ℂ)) * (j1 E r s φ).1 g) = _
        ring
      rw [e]
      refine h.trans (le_of_eq ?_)
      ring
    refine (hCR _ _ ((hφ.tr _).add (hU v)) hb t m).trans ?_
    have hc00 : 0 ≤ c0 := mul_nonneg (abs_nonneg _) (pow_nonneg (mul_nonneg (by linarith) H0) _)
    have hm := pow_nonneg (AutomorphicForm.height_pos m).le N
    rw [abs_of_nonneg (sq_nonneg v)]
    have : C * (c0 * v ^ 2) * Real.exp (R * |t|) * AutomorphicForm.height m ^ N =
        C * (c0 * Real.exp (R * |t|) * AutomorphicForm.height m ^ N * v ^ 2) := by ring
    rw [this]
    have h2 : |C| * c0 * Real.exp (R * |t|) * AutomorphicForm.height m ^ N * v ^ 2 =
        |C| * (c0 * Real.exp (R * |t|) * AutomorphicForm.height m ^ N * v ^ 2) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h : ℝ => slice b.f.1 (t + h) φ.1 m - slice b.f.1 t φ.1 m - h • slice b.f.1 t (j1 E r s φ).1 m) =O[nhds 0]
      fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (|C| * c0 * Real.exp (R * |t|) * AutomorphicForm.height m ^ N) ?_
    have : ∀ᶠ h : ℝ in nhds 0, |h| ≤ 1 := by
      have := Metric.closedBall_mem_nhds (0 : ℝ) one_pos
      filter_upwards [this] with h hh
      simpa using hh
    filter_upwards [this] with h hh
    simpa [Complex.real_smul] using hbig h hh
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
