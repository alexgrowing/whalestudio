import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt

noncomputable section

open MeasureTheory Real
open scoped FourierTransform Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

abbrev V (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n × Fin 2)

def creL : (Fin m → Fin n → ℂ) →ₗ[ℝ] V m n where
  toFun u := WithLp.toLp 2 fun p : Fin m × Fin n × Fin 2 => if p.2.2 = 0 then (u p.1 p.2.1).re else (u p.1 p.2.1).im
  map_add' u v := by
    ext p; simp only [PiLp.add_apply, WithLp.toLp_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl
  map_smul' c u := by
    ext p; simp only [PiLp.smul_apply, WithLp.toLp_smul, Pi.smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> rfl

def cimL : V m n →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun w a j := ⟨w (a, j, 0), w (a, j, 1)⟩
  map_add' w w' := by funext a j; apply Complex.ext <;> simp
  map_smul' c w := by funext a j; apply Complex.ext <;> simp

def Lc : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n :=
  (LinearEquiv.ofLinearMap creL cimL
    (by
      ext w p
      obtain ⟨a, j, k⟩ := p
      fin_cases k <;> simp [creL, cimL])
    (by
      ext u a j <;> simp [creL, cimL])).toContinuousLinearEquiv

theorem inner_Lc (y v : Fin m → Fin n → ℂ) :
    inner ℝ (Lc y) (Lc v) = ∑ a, ∑ j, ((starRingEnd ℂ) (v a j) * y a j).re := by
  have hL : ∀ z : Fin m → Fin n → ℂ, Lc z = creL z := fun _ => rfl
  rw [hL, hL, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_congr rfl]
  intro a _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [creL, Fin.sum_univ_two, Complex.mul_re]

def Dlin (ε : Fin m → Bool) : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
  (LinearEquiv.ofLinearMap
    { toFun := fun u a j => sgn ε a * u a j
      map_add' := fun u v => by funext a j; simp [mul_add]
      map_smul' := fun c u => by funext a j; simp [Complex.real_smul]; ring }
    { toFun := fun u a j => sgn ε a * u a j
      map_add' := fun u v => by funext a j; simp [mul_add]
      map_smul' := fun c u => by funext a j; simp [Complex.real_smul]; ring }
    (by ext u a j <;> simp [sgn] <;> split_ifs <;> simp)
    (by ext u a j <;> simp [sgn] <;> split_ifs <;> simp)).toContinuousLinearEquiv

theorem Dlin_apply (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    Dlin ε u a j = sgn ε a * u a j := rfl

def Mt (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n :=
  ((Dlin ε).trans Lc).trans
    (LinearEquiv.smulOfNeZero ℝ (V m n) (-t / Real.pi)
      (div_ne_zero (neg_ne_zero.2 ht) Real.pi_pos.ne')).toContinuousLinearEquiv

theorem Mt_apply (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (u : Fin m → Fin n → ℂ) :
    Mt ε t ht u = (-t / Real.pi) • Lc (Dlin ε u) := rfl

theorem re_trace_eq (ε : Fin m → Bool) (u y : Fin m → Fin n → ℂ) :
    (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace).re = inner ℝ (Lc y) (Lc (Dlin ε u)) := by
  rw [inner_Lc, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Dlin_apply, map_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := by
    simp only [sgn]; split_ifs <;> simp
  rw [hs, ← Complex.star_def]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring_nf

theorem haar_Lc : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℂ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (Lc y) = (c : ℂ) * ∫ w, F w := by
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (Measure.map (Lc (m := m) (n := n)) volume).IsAddHaarMeasure :=
    (Lc (m := m) (n := n)).isAddHaarMeasure_map volume
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map (Lc (m := m) (n := n)) volume)
    (volume : Measure (V m n))
  set c := (Measure.map (Lc (m := m) (n := n)) volume).addHaarScalarFactor (volume : Measure (V m n)) with hc
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F _ => ?_⟩
  calc ∫ y, F (Lc y) = ∫ w, F w ∂(Measure.map (Lc (m := m) (n := n)) volume) :=
        (integral_map_equiv (Lc (m := m) (n := n)).toHomeomorph.toMeasurableEquiv F).symm
    _ = ∫ w, F w ∂(c • (volume : Measure (V m n))) := by rw [← hmap]
    _ = (c : ℂ) * ∫ w, F w := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem ftLoc_eq (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : SchwartzMap (Fin m → Fin n → ℂ) ℂ) (u : Fin m → Fin n → ℂ),
      ftLoc ε t (⇑S) u = (c : ℂ) * 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S)
        (Mt ε t ht u) := by
  obtain ⟨c, hc, hH⟩ := haar_Lc (m := m) (n := n)
  refine ⟨c, hc, fun S u => ?_⟩
  rw [SchwartzMap.fourier_coe, Real.fourier_eq', ← hH (fun v => Complex.exp (↑(-2 * π * inner ℝ v (Mt ε t ht u)) * Complex.I) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S) v) ?_]
  · simp only [ftLoc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [re_trace_eq, Mt_apply, real_inner_smul_right, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    field_simp
  · fun_prop

theorem isSch_ftLoc (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (κ : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    IsSch (fun u => κ * ftLoc ε t f u) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨c, -, h⟩ := ftLoc_eq (n := n) ε t ht
  refine ⟨(κ * c) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Mt ε t ht)
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S)), ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h,
    smul_eq_mul]
  ring

theorem ftLoc_surj (ε : Fin m → Bool) (t : ℝ) (ht : t ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : IsSch g) :
    ∃ f, IsSch f ∧ (fun u => ftLoc ε t f u) = g := by
  obtain ⟨T, rfl⟩ := hg
  obtain ⟨c, hc, hH⟩ := ftLoc_eq ε t ht
  set G : SchwartzMap (V m n) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Mt ε t ht).symm T with hG
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)) (𝓕⁻ (((c : ℂ)⁻¹) • G)), ⟨_, rfl⟩, ?_⟩
  funext u
  rw [hH]
  have h1 : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)) (𝓕⁻ (((c : ℂ)⁻¹) • G))) =
      𝓕⁻ (((c : ℂ)⁻¹) • G) := by
    ext w
    simp
  rw [h1, FourierInvPair.fourier_fourierInv_eq]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [SchwartzMap.smul_apply, hG, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
  field_simp

theorem ftLoc_neg (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε t f (-u) = ftLoc ε (-t) f u := by
  simp only [ftLoc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hm : Matrix.of (-u) = -Matrix.of u := rfl
  simp only [hm, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re]
  push_cast
  ring_nf

end PositivityTheory.Rg.Sw.Glob.FTD
