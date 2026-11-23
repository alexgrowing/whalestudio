import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PeriodDatum

noncomputable section

lemma lattice_equiv {La : Type} [AddCommGroup La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧
      ∃ e : ℝ ⊗[ℤ] La ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, e (1 ⊗ₜ x) = P x := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  let f : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hinj
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ La := Module.Finite.equiv f.symm
  haveI : Module.Free ℤ La := Module.Free.of_equiv f.symm
  have hr : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [f.finrank_eq, ZLattice.rank ℝ L]
  have hg : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
  let φ : ℝ ⊗[ℤ] La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hφ : ∀ x, φ (1 ⊗ₜ x) = P x := fun x => by simp [φ]
  have hs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hφ x⟩
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] La) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_baseChange, hr]
  exact ⟨inferInstance, hr.trans hg, LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hs, hs⟩, hφ⟩

lemma hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

lemma hermForm_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = starRingEnd ℂ c * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

lemma hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

lemma hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add]

lemma hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    (hermForm Hm z z).im = 0 := by
  have := h.im_star_dotProduct_mulVec_self (star z)
  simpa [hermForm] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma two_mul_eq_of_isTypeFn (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty 1
  have h2 := PeriodNonempty.sum_type H he 1
  simp only [map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Embeddings.card, Nat.cast_one] at h1 h2
  have : (2 * g : ℂ) = Module.finrank ℚ E * (p + q) := by rw [h1, h2]; ring
  exact_mod_cast this

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ))
    (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF →
    (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) →
    ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y) := by
  intro E _ _ _ H La _ _ EF p q g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  classical
  obtain ⟨hfin, hrk, e, he⟩ := lattice_equiv P hinj hdisc hspan
  haveI : Module.Finite (𝓞 E) La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) La
  have htor : Submodule.torsion (𝓞 E) La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have ha0 : (a : E) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    rw [Submodule.mem_bot]
    apply hinj
    funext i
    have h1 := hlin a x i
    have h2 : a • x = 0 := hx
    rw [h2, map_zero] at h1
    rw [map_zero]
    exact (mul_eq_zero.1 h1.symm).resolve_left ((map_ne_zero (ty i)).2 ha0)
  haveI : Module.Flat (𝓞 E) La := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) La := Module.Flat.projective_of_finitePresentation
  have hrank : Module.finrank (𝓞 E) La = p + q := by
    have h1 := finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := La)
    rw [hrk, two_mul_eq_of_isTypeFn H hty, RingOfIntegers.rank] at h1
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1).symm
  have het : ∀ (r : ℝ) x, e (r ⊗ₜ x) = (r : ℂ) • P x := fun r x => by
    rw [← he, Complex.coe_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hB : ∀ x y, EF.baseChange ℝ x y = (hermForm Hm (e x) (e y)).im := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp [hermForm]
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h', hermForm_add_left, Complex.add_im]
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hermForm]
      | add y y' h h' => simp only [map_add, h, h', hermForm_add_right, Complex.add_im]
      | tmul r' y =>
        rw [het, het, hermForm_smul_left, hermForm_smul_right, LinearMap.BilinForm.baseChange_tmul]
        simp [him]
        ring
  let d : (Fin g → ℂ) → Module.End ℂ (Fin g → ℂ) := fun c => Matrix.toLin' (Matrix.diagonal c)
  have hd : ∀ c z i, d c z i = c i * z i := fun c z i => by simp [d, Matrix.mulVec_diagonal]
  have hdt : ∀ c, LinearMap.trace ℝ _ (e.symm.conj ((d c).restrictScalars ℝ)) = 2 * (∑ i, c i).re := fun c => by
    rw [LinearMap.trace_conj', PeriodNonempty.trace_real]
    simp [d]
  let J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La := e.symm.conj ((d fun _ => Complex.I).restrictScalars ℝ)
  have hJ : ∀ x, e (J x) = Complex.I • e x := fun x => by
    funext i
    simp [J, LinearEquiv.conj_apply, hd]
  refine ⟨{ La := La, fin := inferInstance, proj := hproj, EF := EF, alt := fun x => ?_, unimod := hbij,
            adj := hadj, p := p, q := q, rank := hrank, dom := ⟨J, fun x => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩ },
    LinearEquiv.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  · have := him x x
    rw [hermForm_self_im hH] at this
    exact_mod_cast this.symm
  · apply e.injective
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · rw [hB, hB, hJ, hJ, hermForm_smul_left, hermForm_smul_right]
    simp
  · rw [hB, hJ, hermForm_smul_left]
    simpa using hpos (e x) (by simpa using hx)
  · intro a A t hA ht
    rw [← PeriodNonempty.sum_type H hty] at ht
    have hAe : ∀ x i, e (A x) i = ty i (a : E) * e x i := fun x i => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, Pi.add_apply, h, h', mul_add]
      | tmul r x =>
        have : (r ⊗ₜ[ℤ] x : ℝ ⊗[ℤ] La) = r • (1 ⊗ₜ[ℤ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hA, map_smul, map_smul, he, he]
        simp only [Pi.smul_apply, hlin, Complex.real_smul]
        ring
    have h1 : A = e.symm.conj ((d fun i => ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe]
    have h2 : J ∘ₗ A = e.symm.conj ((d fun i => Complex.I * ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe, hJ, mul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp only [LinearMap.comp_apply, hJ, hAe, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [h1, hdt, ht]
    · rw [h2, hdt, ht, ← Finset.mul_sum]
      simp

end

end GlobalTheory.PeriodDatum
