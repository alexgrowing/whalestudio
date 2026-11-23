import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifferenceStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.FibVan

theorem esymm_sub_injective :
    Function.Injective (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) := by
  have e : (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) =
      (symmetricSubalgebra (Fin 2) ℝ).val.comp (esymmAlgHom (Fin 2) ℝ 2) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i
    · simp [esymmAlgHom, esymm, Finset.powersetCard_one, Fin.sum_univ_two]
    · have : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by decide
      simp [esymmAlgHom, esymm, Fin.prod_univ_two, this]
  rw [e]
  exact Subtype.val_injective.comp (esymmAlgHom_fin_injective ℝ le_rfl)

theorem X_sub_X_ne_zero : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  intro h
  have := congrArg (eval ![1, 0]) h
  simp at this

theorem hs_roots (k : ℕ) : aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) =
    (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := GlobalTheory.T.complete_symmetric_mul_difference k

theorem sum_hs_eq_zero (m' : ℕ) : ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
    X 0 ^ (m' + 1 - i) = (0 : MvPolynomial (Fin 2) ℝ) := by
  apply esymm_sub_injective
  rw [map_zero]
  refine (mul_left_injective₀ X_sub_X_ne_zero) ?_
  simp only [zero_mul, map_sum, Finset.sum_mul]
  have key : ∀ c : MvPolynomial (Fin 2) ℝ, ∑ i ∈ Finset.range (m' + 2), (-c) ^ i * (X 0 + X 1) ^ (m' + 1 - i) *
      (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) = (-c + (X 0 + X 1)) ^ (m' + 1) := fun c => (add_pow _ _ _).symm
  have h0 := key (X 0)
  have h1 := key (X 1)
  rw [show -X 0 + (X 0 + X 1) = (X 1 : MvPolynomial (Fin 2) ℝ) by ring] at h0
  rw [show -X 1 + (X 0 + X 1) = (X 0 : MvPolynomial (Fin 2) ℝ) by ring] at h1
  have e : ∀ i ∈ Finset.range (m' + 2), aeval ![X 0 + X 1, X 0 * X 1]
      (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) * X 0 ^ (m' + 1 - i)) * (X 0 - X 1) =
      X 0 ^ (m' + 1) * ((-X 0) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) -
      X 1 ^ (m' + 1) * ((-X 1) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) := by
    intro i _
    have hr := hs_roots (m' + i)
    simp only [map_mul, map_pow, aeval_C, aeval_X, algebraMap_eq, map_neg, map_one, map_natCast, neg_pow (X 0 : MvPolynomial (Fin 2) ℝ),
      neg_pow (X 1 : MvPolynomial (Fin 2) ℝ), Matrix.cons_val_zero]
    linear_combination ((-1 : MvPolynomial (Fin 2) ℝ) ^ i * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) * (X 0 + X 1) ^ (m' + 1 - i)) * hr
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1]
  ring

end GlobalTheory.FibVan

noncomputable section

namespace GlobalTheory.FibVan

section Gen
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fldHom : (A.Pt → Ev n) →ₐ[ℂ] A.Fld := AlgHom.compLeft (Subalgebra.center ℂ (Alt n)).val A.Pt

theorem fldHom_apply (u : A.Pt → Ev n) : fldHom A u = fld A u := rfl

theorem fldHom_comm (u : A.Pt → Ev n) (β : A.Fld) : β * fldHom A u = fldHom A u * β := by
  funext x
  exact Subalgebra.mem_center_iff.mp (u x).2 (β x)

def xi {ι : Type} (w : ι → A.Pt → Ev n) : MvPolynomial ι ℝ →+* A.Fld :=
  (fldHom A).toRingHom.comp ((aeval w).toRingHom.comp (MvPolynomial.map (algebraMap ℝ ℂ)))

theorem xi_apply {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) :
    xi A w Q = fldHom A (aeval w (Q.map (algebraMap ℝ ℂ))) := rfl

theorem evalF_eq_xi {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) : evalF A w Q = xi A w Q := by
  funext x
  rw [xi_apply, fldHom_apply]
  show ((aeval (fun i => w i x) (Q.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = ((aeval w (Q.map (algebraMap ℝ ℂ)) x : Ev n) : Alt n)
  congr 1
  rw [show (aeval w (Q.map (algebraMap ℝ ℂ)) x) = Pi.evalAlgHom ℂ (fun _ => Ev n) x (aeval w (Q.map (algebraMap ℝ ℂ))) from rfl,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem xi_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : xi A w (X i) = fldHom A (w i) := by
  simp [xi_apply]

theorem xi_C {ι : Type} (w : ι → A.Pt → Ev n) (r : ℝ) : xi A w (C r) = algebraMap ℂ A.Fld (r : ℂ) := by
  simp [xi_apply]

theorem isForm_xi {ι : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (Q : MvPolynomial ι ℝ) :
    A.IsForm (xi A w Q) := by
  rw [← evalF_eq_xi]
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1

theorem isForm_mul {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α * β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).2.1

theorem isForm_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α + β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).1

theorem isForm_smul (c : ℂ) {α : A.Fld} (hα : A.IsForm α) : A.IsForm (c • α) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 c α α hα hα).2.2.1

theorem isForm_one : A.IsForm 1 := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1

theorem isForm_zero : A.IsForm 0 := by simpa using isForm_smul A 0 (isForm_one A)

theorem isForm_pow {α : A.Fld} (hα : A.IsForm α) (j : ℕ) : A.IsForm (α ^ j) := by
  induction j with
  | zero => simpa using isForm_one A
  | succ j ih => rw [pow_succ]; exact isForm_mul A ih hα

theorem isForm_sum {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.IsForm (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isForm_zero A
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isForm_add A (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Gen

section Lin
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

theorem integral_add' {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have hi : ∀ γ : A.Fld, A.IsForm γ → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part γ ε) := fun γ hγ ε => by
    haveI := hfin γ hγ ε
    exact integrable_const _
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  exact (hadd _ α β hα hβ (hi α hα) (hi β hβ)).2

theorem integral_smul' (t : ℝ) {α : A.Fld} (hα : A.IsForm α) : A.integral ((t : ℂ) • α) = t * A.integral α := by
  obtain ⟨-, -, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact hsm _ t α hα

theorem integral_zero' : A.integral 0 = 0 := by
  have := integral_smul' A 0 (isForm_one A)
  simpa using this

theorem integral_sum' {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.integral (∑ i ∈ s, f i) = ∑ i ∈ s, A.integral (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using integral_zero' A
  | insert a s ha ih =>
    have hs : A.IsForm (∑ i ∈ s, f i) := isForm_sum A s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add' A (hf a (by simp)) hs,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end Lin

end GlobalTheory.FibVan

end

noncomputable section

namespace GlobalTheory.FibVan

theorem pow_succ_of_sq_zero' {R : Type} [CommRing R] (t ω : R) (n : ℕ) :
    ∃ r : R, t ^ (n + 1) = (t + ω) ^ (n + 1) - ((n : R) + 1) * (ω * (t + ω) ^ n) + ω * ω * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨((n : R) + 1) * (t + ω) ^ n + t * r, ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

theorem expand_pow {R : Type} [CommRing R] (t e : R) (m : ℕ) :
    (t * (e - t)) ^ m = ∑ i ∈ Finset.range (m + 1), ((-1) ^ i * (m.choose i : R)) * (t ^ (m + i) * e ^ (m - i)) := by
  rw [mul_pow, show e - t = -t + e by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]
  ring

def pullHom {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p) :
    (hB.atlas σ).Fld →+* (hY.atlas σ).Fld where
  toFun := pullF hB hY σ π w
  map_one' := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).1
  map_mul' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).2.1
  map_zero' := by
    have := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
      ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 0 0).2.2.1
    simp only [zero_smul] at this
    exact this
  map_add' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).1

section Pull
variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p)

theorem pullHom_apply (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w α = pullF hB hY σ π w α := rfl

theorem pullHom_smul (c : ℂ) (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w (c • α) = c • pullHom hB hY σ π w α :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 c α α).2.2.1

theorem pullHom_algebraMap (c : ℂ) : pullHom hB hY σ π w (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  rw [Algebra.algebraMap_eq_smul_one, pullHom_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

theorem isForm_pullHom {α : (hB.atlas σ).Fld} (hα : (hB.atlas σ).IsForm α) : (hY.atlas σ).IsForm (pullHom hB hY σ π w α) :=
  ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α α).2.2.2 hα).1

end Pull

theorem fibre_integral_vanish : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (pullF hB hY σ π w φ * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ phi hφ ι s m W
  haveI := hB.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  haveI := hY.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have glob := fun χ hχ n => GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ χ hχ n
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨bB1, bB2, -⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨-, hpc1, -⟩ := (GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p (d + 1) hY π w
  set P := pullHom hB hY σ π w with hP
  set x5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx5
  set f4 : Fin 4 → (hB.atlas σ).Pt → Ev d := fam4 hB σ H flB A with hf4
  set om : (hY.atlas σ).Pt → Ev (d + 1) := omF hY σ (h.pull π w) fl with hom
  have hom2 : om * om = 0 := (bY2 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1
  have fx5 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x5 i)) := fun i => (bY1 _ (fam5 π w H flB fl A i)).1.1
  have ff4 : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (f4 i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have fom : (hY.atlas σ).IsForm (fld (hY.atlas σ) om) := (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1

  have hbr : ∀ Q : MvPolynomial (Fin 3) ℝ, xi (hY.atlas σ) x5 (aeval ![X 2, X 3, X 4] Q) = P (xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] Q)) := by
    intro Q
    have e : (xi (hY.atlas σ) x5).comp (aeval ![X 2, X 3, X 4] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toRingHom =
        P.comp ((xi (hB.atlas σ) f4).comp (aeval ![X 0, X 1, X 2] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ).toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
          algebraMap_eq, xi_C]
        rw [pullHom_algebraMap]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        fin_cases j
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 A
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
        · simp only [Fin.reduceFinMk, Matrix.cons_val, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
    exact congrArg (fun f => f Q) e

  have hc6 : ∀ (Q : MvPolynomial (Fin 6) ℝ) (β : (hY.atlas σ).Fld), β * xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q =
      xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q * β := fun Q β => fldHom_comm (hY.atlas σ) _ β
  obtain ⟨x6, hx6⟩ : ∃ x6 : Fin 6 → (hY.atlas σ).Pt → Ev (d + 1), x6 = Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om := ⟨_, rfl⟩
  rw [← hx6] at hc6
  have hx6i : ∀ i : Fin 5, x6 i.castSucc = x5 i := fun i => by rw [hx6]; exact Fin.snoc_castSucc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _ _
  have h5 : x6 5 = om := by rw [hx6]; exact Fin.snoc_last (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _
  have f6 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x6 i)) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show x6 (Fin.last 5) = om from h5]; exact fom
    · rw [hx6i]; exact fx5 j
  have xi6_0 : xi (hY.atlas σ) x6 (X 0) = fld (hY.atlas σ) (x5 0) := by rw [xi_X, fldHom_apply, show x6 0 = x5 0 from hx6i 0]
  have xi6_5 : xi (hY.atlas σ) x6 (X 5) = fld (hY.atlas σ) om := by rw [xi_X, fldHom_apply, h5]
  have xi6_sq : xi (hY.atlas σ) x6 (X 5 * X 5) = 0 := by
    rw [map_mul, xi_X, h5, ← map_mul]
    exact (congrArg (fldHom (hY.atlas σ)) hom2).trans (map_zero _)
  have hren : ∀ Q : MvPolynomial (Fin 5) ℝ, xi (hY.atlas σ) x5 Q = xi (hY.atlas σ) x6 (rename Fin.castSucc Q) := by
    intro Q
    have e : xi (hY.atlas σ) x5 = (xi (hY.atlas σ) x6).comp (rename Fin.castSucc : MvPolynomial (Fin 5) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp [xi_C]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, xi_X, hx6i]
    exact congrArg (fun f => f Q) e
  have heps6 : xi (hY.atlas σ) x6 (X 3 + X 4) = P (xi (hB.atlas σ) f4 (X 1 + X 2)) := by
    have hh := hbr (X 1 + X 2)
    have l : aeval ![X 2, X 3, X 4] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 3 + X 4 : MvPolynomial (Fin 5) ℝ) := by simp
    have r : aeval ![X 0, X 1, X 2] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 1 + X 2 : MvPolynomial (Fin 4) ℝ) := by simp
    rw [l, r, hren] at hh
    rw [← hh]
    congr 1
    simp only [map_add, rename_X]
    rfl
  have fε : (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (X 1 + X 2)) := isForm_xi (hB.atlas σ) f4 ff4 _
  have KY1 : ∀ (n : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ) =
      -(hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
    intro n χ hχ
    obtain ⟨R, hR⟩ := pow_succ_of_sq_zero' (X 0 : MvPolynomial (Fin 6) ℝ) (X 5) n
    have g1 : (hY.atlas σ).integral ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) = 0 := (glob χ hχ (n + 1)).1
    have g2 : (hY.atlas σ).integral (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) =
        1 / (n + 1 : ℝ) * (hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
      rw [← evalF_eq_xi]; exact (glob χ hχ n).2
    have key : xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ = (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ +
        ((-((n : ℝ) + 1) : ℝ) : ℂ) • (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) := by
      rw [hR, map_add, map_mul (xi (hY.atlas σ) x6) (X 5 * X 5) R, xi6_sq, zero_mul, add_zero]
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_one, xi6_0, xi6_5]
      rw [Algebra.smul_def, hP, pullHom_apply]
      simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, map_neg, map_add,
        map_natCast, map_one]
      noncomm_ring
    have f1 : (hY.atlas σ).IsForm ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _) (isForm_pullHom hB hY σ π w hχ)
    have f2 : (hY.atlas σ).IsForm (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_mul (hY.atlas σ) fom (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _)) (isForm_pullHom hB hY σ π w hχ)
    rw [key, integral_add' (hY.atlas σ) f1 (isForm_smul (hY.atlas σ) _ f2), integral_smul' (hY.atlas σ) _ f2, g1, g2]
    field_simp
    ring
  have KY : ∀ (j : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ j) * P χ) = 0 := by
    intro j χ hχ
    rcases j with _ | m'
    · have := (glob χ hχ 0).1
      simpa [hP, pullHom_apply] using this
    · have hexp : (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ (m' + 1) =
          ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i)) := by
        rw [expand_pow]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show m' + 1 + i = m' + i + 1 by omega]
        simp [map_mul, map_pow, map_neg, map_natCast]
      have hterm : ∀ i ∈ Finset.range (m' + 2), xi (hY.atlas σ) x6 (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) *
          (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i))) * P χ = ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) := by
        intro i _
        rw [map_mul (xi (hY.atlas σ) x6) (C _) _, map_mul (xi (hY.atlas σ) x6) (X 0 ^ _) _, map_pow (xi (hY.atlas σ) x6) (X 3 + X 4), heps6, xi_C, Algebra.smul_def,
          map_mul P, map_pow P]
        simp only [mul_assoc]
      have fZ : ∀ i ∈ Finset.range (m' + 2), (hY.atlas σ).IsForm (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hY.atlas σ) (isForm_xi (hY.atlas σ) x6 f6 _)
          (isForm_pullHom hB hY σ π w (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ))
      rw [hexp, map_sum, Finset.sum_mul, Finset.sum_congr rfl hterm,
        integral_sum' (hY.atlas σ) _ (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
          (fun i hi => isForm_smul (hY.atlas σ) _ (fZ i hi))]
      rw [Finset.sum_congr rfl (fun i hi => by rw [integral_smul' (hY.atlas σ) _ (fZ i hi), KY1 _ _ (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)])]
      have fB : ∀ i ∈ Finset.range (m' + 2), (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) *
          (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hB.atlas σ) (isForm_xi (hB.atlas σ) f4 ff4 _) (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)
      have hsumB : ∑ i ∈ Finset.range (m' + 2), ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) =
          xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
            X 0 ^ (m' + 1 - i))) * χ := by
        rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, algebraMap_eq, xi_C,
          Algebra.smul_def]
        simp only [mul_assoc]
      have h0 := integral_sum' (hB.atlas σ) (Finset.range (m' + 2)) (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
        (fun i hi => isForm_smul (hB.atlas σ) _ (fB i hi))
      rw [hsumB, sum_hs_eq_zero, map_zero, map_zero, zero_mul, integral_zero'] at h0
      rw [Finset.sum_congr rfl (fun i hi => integral_smul' (hB.atlas σ) _ (fB i hi))] at h0
      simp only [mul_neg, Finset.sum_neg_distrib, ← h0, neg_zero]
  rw [evalF_eq_xi, upperParabolic, map_sum, Finset.mul_sum]
  rw [integral_sum' (hY.atlas σ) s (fun x => pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)))
    (fun x _ => isForm_mul (hY.atlas σ) (isForm_pullHom hB hY σ π w hφ) (isForm_xi (hY.atlas σ) x5 fx5 _))]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hA : rename Fin.castSucc ((X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) ^ m x) =
      (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ m x := by
    simp only [map_pow, map_mul, map_sub, map_add, rename_X]
    rfl
  have hx : pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)) =
      xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ m x) * P (phi * xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] (W x))) := by
    rw [map_mul, hbr, hren, hA, ← mul_assoc, hc6, mul_assoc, map_mul P]
    rfl
  rw [hx]
  exact KY _ _ (isForm_mul (hB.atlas σ) hφ (isForm_xi (hB.atlas σ) f4 ff4 _))

end GlobalTheory.FibVan

end
