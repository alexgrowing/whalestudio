import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEvalFormModRelationEqStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineGysin

section Atlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem fld_add (u v : A.Pt → Ev n) : fld A (u + v) = fld A u + fld A v := by
  funext x; simp [fld]

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_C {ι : Type} (w : ι → A.Pt → Ev n) (a : ℝ) :
    evalF A w (C a) = ((a : ℂ)) • (1 : A.Fld) := by
  funext x
  simp only [evalF, fld, map_C, aeval_C, Pi.smul_apply, Pi.one_apply]
  first
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]; rfl)
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, Complex.coe_algebraMap])
  | (simp [Algebra.algebraMap_eq_smul_one, -Complex.coe_smul])

theorem evalF_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x; simp [evalF, fld]

theorem evalF_one {ι : Type} (w : ι → A.Pt → Ev n) : evalF A w 1 = 1 := by
  funext x; simp [evalF, fld]

theorem evalF_rename {ι κ : Type} (w : κ → A.Pt → Ev n) (e : ι → κ) (P : MvPolynomial ι ℝ) :
    evalF A w (rename e P) = evalF A (fun i => w (e i)) P := by
  funext x; simp [evalF, fld, map_rename, aeval_rename, Function.comp_def]

end Atlas

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

section Int

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

theorem integral_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  refine (L.2.1 _ α β hα hβ (fun ε => ?_) (fun ε => ?_)).2
  · haveI := L.1 α hα ε; exact integrable_const _
  · haveI := L.1 β hβ ε; exact integrable_const _

theorem integral_smul (t : ℝ) {α : A.Fld} (hα : A.IsForm α) :
    A.integral ((t : ℂ) • α) = t * A.integral α := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact L.2.2.1 _ t α hα

end Int

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

theorem dvd_swap (t : ℝ) (T : MvPolynomial (Fin 3) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      rename (![1, 2, 0] : Fin 3 → Fin 4) (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T) -
        C t * X 1 * aeval ![X 1 + X 2, X 3, X 0] T := by
  set I : Ideal (MvPolynomial (Fin 4) ℝ) := Ideal.span {X 3 - X 1 * X 2}
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk ℝ]
  have h1 : ∀ g : Fin 3 → MvPolynomial (Fin 4) ℝ,
      Ideal.Quotient.mkₐ ℝ I (aeval g T) = aeval (fun j => Ideal.Quotient.mkₐ ℝ I (g j)) T := fun g => by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h2 : ∀ g : Fin 3 → MvPolynomial (Fin 3) ℝ,
      rename (![1, 2, 0] : Fin 3 → Fin 4) (aeval g T) = aeval (fun j => rename (![1, 2, 0] : Fin 3 → Fin 4) (g j)) T :=
    fun g => by rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h3 : Ideal.Quotient.mkₐ ℝ I (X 1 * X 2) = Ideal.Quotient.mkₐ ℝ I (X 3) := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.2 ⟨-1, by ring⟩
  simp only [map_mul, rename_C, rename_X, h2]
  rw [h1, h1]
  congr 1
  refine congrArg (fun f => aeval f T) ?_
  funext j
  fin_cases j
  · simp
  · simpa [Ideal.Quotient.mkₐ_eq_mk] using h3
  · simp

theorem gysin : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ (t : ℝ) (T : MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (evalF (hY.atlas σ) (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i))
          (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T)) =
        -t * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ t T
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨bB1, bB2, bB3⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hol, hc1, hE⟩ := bB3 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)
  have cY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  have pl := cB.2.2.2.2 _ _ (hY.atlas σ) _ hol
  simp only [pullF] at hc1 hc2
  have gens : ∀ i : Fin 3, evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (![X 1 + X 2, X 3, X 0] i) =
      pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (![X 1 + X 2, X 3, X 0] i)) := by
    intro i
    simp only [pullF]
    fin_cases i
    · change evalF _ _ (X 1 + X 2) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 1 + X 2))
      rw [evalF_add,
        evalF_add, evalF_X, evalF_X, evalF_X, evalF_X]
      change fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) + fld _ (c1F hY σ (VMetric.grLB fl 1 (H.pull π w))) =
        (hB.atlas σ).pullback _ _ (fld _ (c1F hB σ (VMetric.grLB flB 0 H)) + fld _ (c1F hB σ (VMetric.grLB flB 1 H)))
      rw [← fld_add, hsum, fld_add, hc1, hc1, (pl.2 0 _ _).1]
    · change evalF _ _ (X 3) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 3))
      rw [evalF_X, evalF_X]
      exact hc2
    · change evalF _ _ (X 0) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 0))
      rw [evalF_X, evalF_X]
      exact hc1 A
  have hpull : ∀ P : MvPolynomial (Fin 3) ℝ,
      evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (aeval ![X 1 + X 2, X 3, X 0] P) =
        pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] P)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, MvPolynomial.algebraMap_eq, evalF_C, pullF]
      rw [(pl.2 _ 1 1).2.2.1, pl.1]
    | add P Q hP hQ =>
      rw [map_add, evalF_add, evalF_add, hP, hQ]
      simp only [pullF]
      rw [(pl.2 0 _ _).1]
    | mul_X P i hP =>
      rw [map_mul, evalF_mul, evalF_mul, hP, aeval_X, gens i]
      simp only [pullF]
      rw [(pl.2 0 _ _).2.1]
  have e3 : (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i)) =
      fun i => fam4 hY σ (H.pull π w) fl (A.pull π w) ((![1, 2, 0] : Fin 3 → Fin 4) i) := by
    funext i; fin_cases i <;> rfl
  rw [e3, ← evalF_rename,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k Y p (d + 1) hY _ (h.pull π w) (H.pull π w) fl (A.pull π w) σ _ _ (dvd_swap t T),
    evalF_mul, evalF_mul, evalF_C, evalF_X, hpull]

  have hcB : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (fam4 hB σ H flB A i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have hφ := (cB.2.2.2.1 (Fin 4) _ (aeval ![X 1 + X 2, X 3, X 0] T) hcB).1
  have hpφ : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))) :=
    ((pl.2 0 _ 0).2.2.2 hφ).1
  have hx0 : (hY.atlas σ).IsForm (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))) := (bY1 _ (A.pull π w)).1.1
  have hom : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) :=
    (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have G := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl ‹_› A σ _ hφ
  have G1 := (G 1).1
  have G0 := (G 0).2
  rw [hs, pow_zero, mul_one] at G0
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.choose_zero_right, mul_one, Nat.cast_one, map_one,
    Nat.sub_zero, Nat.mul_zero, Nat.zero_sub, Nat.choose_self, one_mul, evalF_one, CharP.cast_eq_zero, zero_add,
    div_one, MvPolynomial.C_1] at G0
  rw [pow_one] at G1
  set x0 := fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))
  set om := fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)
  set pφ := pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))
  have key : (t : ℂ) • (1 : (hY.atlas σ).Fld) * fld (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w) 1) * pφ =
      (t : ℂ) • ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := by
    rw [smul_mul_assoc, one_mul, smul_mul_assoc]
    congr 1
    rw [add_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, add_neg_cancel_right]
    rfl
  have f1 : (hY.atlas σ).IsForm ((x0 + om) * pφ) := (cY.2.1 0 _ _ (cY.2.1 0 _ _ hx0 hom).1 hpφ).2.1
  have f2 : (hY.atlas σ).IsForm (om * pφ) := (cY.2.1 0 _ _ hom hpφ).2.1
  have f3 : (hY.atlas σ).IsForm (((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 _ _ _ f2 f2).2.2.1
  have f4 : (hY.atlas σ).IsForm ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 0 _ _ f1 f3).1
  rw [key, integral_smul _ _ f4, integral_add _ f1 f3, integral_smul _ _ f2, G1, G0]
  ring

end GlobalTheory.LineGysin
