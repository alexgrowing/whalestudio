import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

private theorem ht_zt (t : ℝ) : AutomorphicForm.height (zt E r t) ≤
    Real.exp |t| ^ (2 * Fintype.card (InfinitePlace E)) := by
  set e : ℝ := ((r * Module.finrank ℚ E : ℝ))⁻¹ with he
  have hL : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ Real.exp |t| → x ^ e ≤ Real.exp |t| := fun x hx hxL =>
    calc x ^ e ≤ Real.exp |t| ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ Real.exp |t| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = Real.exp |t| := Real.rpow_one _
  refine CuspidalSpectrum.height_diagUnits_posIdele_le (K := E) (n := r) (ρ := fun _ => Real.exp t ^ e)
    (fun _ => Real.rpow_pos_of_pos (Real.exp_pos t) e) hL
    fun _ => ⟨key _ (Real.exp_pos t).le (Real.exp_le_exp.2 (le_abs_self t)), ?_⟩
  rw [← Real.inv_rpow (Real.exp_pos t).le, ← Real.exp_neg]
  exact key _ (Real.exp_pos _).le (Real.exp_le_exp.2 (neg_le_abs t))

private theorem ct_bd (n r N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : AdelicGLn.AdelicGL E n → ℂ) (B : ℝ), 0 ≤ B →
    (∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) →
    ∀ g, ‖constantTerm r φ g‖ ≤ C * B * AutomorphicForm.height g ^ N := by
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst E n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨(heightConst E n * |M|) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), by positivity,
    fun φ B hB hφ g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain E n r,
      ‖φ (unipGL X * g)‖ ≤ B * (heightConst E n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h1 N) hB)
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst E n * |M|)]
  ring

private theorem F_left {φ : AdelicGLn.AdelicGL E (r + s) → ℂ} (hφ : IsLeftInvariant φ) (t : ℝ)
    (m : AdelicGLn.AdelicGL E s) :
    IsLeftInvariant fun x : AdelicGLn.AdelicGL E r => constantTerm r φ (lev (Ad E) r s (zt E r t * x, m)) := by
  intro γ x
  have h := Pair.ct_lev_rat hφ γ 1 (zt E r t * x) m
  rw [map_one, one_mul] at h
  have e : zt E r t * (AdelicGLn.diagonal E r γ * x) = AdelicGLn.diagonal E r γ * (zt E r t * x) := by
    rw [← mul_assoc, ← mul_assoc, zt, centralSection_mul_comm]
  beta_reduce
  rw [e, h]

private theorem F_bd (r s N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : AdelicGLn.AdelicGL E (r + s) → ℂ) (B : ℝ), 0 ≤ B →
    (∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ (t : ℝ) (m : AdelicGLn.AdelicGL E s)
    (x : AdelicGLn.AdelicGL E r), ‖constantTerm r φ (lev (Ad E) r s (zt E r t * x, m))‖ ≤
      (C * B * Real.exp (((2 * Fintype.card (InfinitePlace E) * N : ℕ) : ℝ) * |t|) * AutomorphicForm.height m ^ N) *
        AutomorphicForm.height x ^ N := by
  obtain ⟨C, hC0, hC⟩ := ct_bd (E := E) (r + s) r N
  have h1 : 0 ≤ heightConst E (r + s) := le_trans zero_le_one one_le_heightConst
  have h2 : 0 ≤ heightConst E r := le_trans zero_le_one one_le_heightConst
  refine ⟨C * (heightConst E (r + s) * heightConst E r) ^ N, by positivity, fun φ B hB hφ t m x => ?_⟩
  have h3 : AutomorphicForm.height (K := E) (lev (Ad E) r s (zt E r t * x, m)) ≤ heightConst E (r + s) *
      (heightConst E r * Real.exp |t| ^ (2 * Fintype.card (InfinitePlace E)) * AutomorphicForm.height x) *
      AutomorphicForm.height m :=
    (Pair.height_lev _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht_zt t) h2) (height_pos _).le)) h1) (height_pos _).le)
  refine (hC φ B hB hφ _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h3 N)
    (mul_nonneg hC0 hB)).trans_eq ?_)
  rw [Real.exp_nat_mul, pow_mul (Real.exp |t|) _ N]
  simp only [mul_pow]
  ring

variable [IsTotallyComplex E] {S : Set (Pl E)}

private theorem sl_int (b : Blo S r) (φ : Sm E (r + s)) (hφ : Umg φ) (t : ℝ) (m : AdelicGLn.AdelicGL E s) :
    Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      constantTerm r φ.1 (lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r), m)) *
        starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r)))
      (quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  have hcφ : Continuous φ.1 := ((umgOps E (r + s)).2 φ hφ).1
  obtain ⟨hfU, hfC⟩ := cuspUmg E r b.f b.cusp
  have hcf : Continuous b.f.1 := ((umgOps E r).2 b.f hfU).1
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨B, hB⟩ := hN 1
  have hB' : ∀ g, ‖φ.1 g‖ ≤ |B| * AutomorphicForm.height g ^ N := fun g =>
    (show ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N by simpa using hB g).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (height_pos _).le N))
  obtain ⟨C, -, hC⟩ := F_bd (E := E) r s N
  obtain ⟨D, hD⟩ := rapidDecay E r b.f hfU hfC N
  exact Pair.pair_int (F_left hφ.left t m) hfU.left
    ((UpperTheory.continuous_constantTerm E (r + s) r φ.1 hcφ).comp
      (Pair.continuous_lev.comp ((continuous_const.mul continuous_id).prodMk continuous_const))) hcf
    (fun x => hC φ.1 _ (abs_nonneg B) hB' t m x) hD

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.sliceBound :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceBound E := by
  intro E _ _ _ S r s b
  refine ⟨fun N => ?_, fun φ ψ c hφ hψ t m => ?_⟩
  · obtain ⟨hfU, hfC⟩ := cuspUmg E r b.f b.cusp
    obtain ⟨C, hC0, hC⟩ := F_bd (E := E) r s N
    obtain ⟨D, hD⟩ := rapidDecay E r b.f hfU hfC N
    have hfin := isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
    refine ⟨C * 2 ^ N * D * (quotientMeasure (rationalGLOne E r) (mu1 E r)).real Set.univ,
      ((2 * Fintype.card (InfinitePlace E) * N : ℕ) : ℝ), fun φ B hφ hB t m => ?_⟩
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 1)) (pow_pos (height_pos _) N)
    have hm := (height_pos (K := E) m).le
    refine (norm_integral_le_of_norm_le_const (.of_forall fun y =>
      Pair.pair_le (F_left hφ.left t m) (by positivity) (fun x => hC φ.1 B hB0 hB t m x) hD _)).trans_eq ?_
    ring
  · have hcφ : Continuous φ.1 := ((umgOps E (r + s)).2 φ hφ).1
    have hcψ : Continuous ψ.1 := ((umgOps E (r + s)).2 ψ hψ).1
    have e : ∀ g, constantTerm r (c • φ + ψ).1 g = c * constantTerm r φ.1 g + constantTerm r ψ.1 g := fun g => by
      rw [← smul_eq_mul, ← constantTerm_smul, ← constantTerm_add (hcφ.const_smul c) hcψ]
      rfl
    simp only [slice, e, add_mul, mul_assoc c]
    rw [integral_add ((sl_int b φ hφ t m).const_mul c) (sl_int b ψ hψ t m), integral_const_mul]
