import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EContJoin

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def E_L (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ) (t : ℝ) :
    (GA E N → ℂ) →ₗ[ℂ] (GA E N → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun g => aT E N r t * g

theorem E_L_apply {N r : ℕ} (t : ℝ) (f : GA E N → ℂ) (g : GA E N) : E_L E N r t f g = f (aT E N r t * g) := rfl

theorem constant_term_zero_eq {N r : ℕ} (f : GA E N → ℂ) : E_L E N r 0 f = f := by
  funext g
  rw [E_L_apply, aT_zero, one_mul]

theorem E_LL {N r : ℕ} (s t : ℝ) (f : GA E N → ℂ) : E_L E N r s (E_L E N r t f) = E_L E N r (t + s) f := by
  funext g
  rw [E_L_apply, E_L_apply, E_L_apply, aT_add, mul_assoc]

variable {r s : ℕ}

theorem E_key_left {r₁ : ℕ} (hr₁ : r₁ < r) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E r → ℂ) (m₂ : GA E s) (h : GA E (r + s)) (hψF : ∀ m₁, ψ m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₁ ψ = E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a (An.ctn r₁ φ.1) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  funext m₁
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_top hr₁ x hx
    omega
  have e2 : ∀ A : UPos r r₁ → Ad E, ψ (unipGL A * m₁) = ∑ t ∈ τs, a t *
      An.ctn r φ.1 (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)) := by
    intro A
    rw [hψF, hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : lev (Ad E) r s (unipGL A * m₁, m₂) = lev (Ad E) r s (unipGL A, 1) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_left r s r₁ hr₁, mul_assoc, ← mul_assoc (aT E (r + s) r t), aT_comm_parGL _ _ _ _ hpos,
      mul_assoc]
  have e3 : ∀ z, ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r x} => boxMeasure E) =
      (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) r₁ * ∫ b, An.ctn r₁ φ.1 (parGL (joinPos (r := r₁) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} => boxMeasure E)) := by
    intro z
    simp only [E_ctn_eq r]
    rw [integral_const_mul, ← constantTermPar_eq_top hr₁ hφc, constantTermPar_eq_bot hr₁ hφc hφl]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext b
    exact E_ct_eq r₁ _ _
  have hint : ∀ t ∈ τs, Integrable (fun A : UPos r r₁ → Ad E => a t * An.ctn r φ.1
      (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)))
      (Measure.pi fun _ => boxMeasure E) := by
    intro t _
    refine (integrable_box ?_).const_mul _
    exact hcr.comp ((((E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r).comp
      (continuous_pi fun q => continuous_apply _))).mul continuous_const)
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [integral_finsetSum _ hint]
  simp only [integral_const_mul, E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_box_reindex (eL r s r₁ hr₁)
    (fun b => An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * y))), e3]
  ring

theorem E_hB_left {r₁ : ℕ} (hr₁ : r₁ < r) (m₂ : GA E s) (h : GA E (r + s)) (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (t : ℝ) (f : GA E (r + s) → ℂ) :
    E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E => (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a (E_L E (r + s) r₁ t f) =
    E_L E r r₁ t (E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a f) := by
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r₁ x → ((x.1.1 : ℕ) < r₁ ↔ (x.1.2 : ℕ) < r₁) := fun x hx => by
    have := E_pos_bot hr₁ x hx
    omega
  funext m₁
  rw [E_L_apply]
  unfold E_B
  refine congrArg (κ * ·) (Finset.sum_congr rfl fun u _ => congrArg (a u * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) r₁ t * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) r₁ t), aT_comm, mul_assoc,
    ← mul_assoc (aT E (r + s) r₁ t), ← lev_aT_left r s r₁ hr₁.le, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem E_trans_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (w : GA E (r + s)) :
    ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * w)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * w)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E)) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hpq : r < r + r₂ := by omega
  simp only [E_ctn_eq r]
  rw [integral_const_mul, ← constantTermPar_eq_bot hpq hφc hφl, constantTermPar_eq_top hpq hφc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext b
  exact E_ct_eq (r + r₂) _ _

theorem E_int_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (z : GA E (r + s)) :
    ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    ∑ t ∈ τs, a t * ((E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * (aT E (r + s) r t * z))
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E))) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have e1 : ∀ b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E, F (parGL (joinPos (r := r) 0 b) * z) =
      ∑ t ∈ τs, a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z)) := by
    intro b
    rw [hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc]
  have hint : ∀ t ∈ τs, Integrable (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E =>
      a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))) (Measure.pi fun _ => boxMeasure E) :=
    fun t _ => (integrable_box (hcr.comp
      ((E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) r).mul continuous_const))).const_mul _
  simp only [e1]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, E_trans_right hr₂ φ hφ]

theorem E_G_shift {r₂ : ℕ} (hr₂ : 0 < r₂) (τs : Finset ℝ) (a : ℝ → ℂ) (u : ℝ) (f : GA E (r + s) → ℂ)
    (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (E_L E (r + s) (r + r₂) u f) z =
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (aT E (r + s) (r + r₂) u * z) := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop (r + r₂) x →
      ((x.1.1 : ℕ) < r + r₂ ↔ (x.1.2 : ℕ) < r + r₂) := fun x hx => by
    have := E_pos_top hpq x hx
    omega
  unfold E_B
  refine congrArg (1 * ·) (Finset.sum_congr rfl fun t _ => congrArg (a t * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) (r + r₂) u * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) (r + r₂) u), aT_comm, mul_assoc]

theorem E_aT_right {r₂ : ℕ} (hr₂s : r₂ ≤ s) (t : ℝ) (m₁ : GA E r) (m₂ : GA E s) (h : GA E (r + s)) :
    aT E (r + s) (r + r₂) t * (lev (Ad E) r s (m₁, m₂) * h) =
      aT E (r + s) r t * (lev (Ad E) r s (m₁, aT E s r₂ t * m₂) * h) := by
  have e1 : aT E (r + s) (r + r₂) t = lev (Ad E) r s (1, aT E s r₂ t) * aT E (r + s) r t := by
    rw [lev_aT_right r s r₂ hr₂s, mul_assoc, ← aT_add, neg_add_cancel, aT_zero, mul_one]
  have e2 : lev (Ad E) r s (m₁, aT E s r₂ t * m₂) = lev (Ad E) r s (1, aT E s r₂ t) * lev (Ad E) r s (m₁, m₂) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, e2, (aT_comm_lev r s t _).symm]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.SliceClasses

end
