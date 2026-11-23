import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFifthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LogSinElim

section Alg

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)

theorem evalF_add' (P Q : MvPolynomial ι ℝ) : evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, AddMemClass.coe_add]

theorem evalF_mul' (P Q : MvPolynomial ι ℝ) : evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, MulMemClass.coe_mul]

theorem evalF_sub' (P Q : MvPolynomial ι ℝ) : evalF A w (P - Q) = evalF A w P - evalF A w Q := by
  funext x
  simp only [evalF, fld, map_sub, Pi.sub_apply, AddSubgroupClass.coe_sub]

theorem evalF_X' (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x
  simp [evalF, fld]

theorem evalF_C' (r : ℝ) : evalF A w (C r) = (r : ℂ) • (1 : A.Fld) := by
  funext x
  simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
  rfl

theorem evalF_aeval_self (s : ι → MvPolynomial ι ℝ) (hs : ∀ i, fld A (w i) = evalF A w (s i))
    (P : MvPolynomial ι ℝ) : evalF A w P = evalF A w (aeval s P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [evalF_C']
  | add P Q hP hQ => rw [map_add, evalF_add', evalF_add', hP, hQ]
  | mul_X P i hP => rw [map_mul, evalF_mul', evalF_mul', hP, aeval_X, evalF_X', hs]

end Alg

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

section Pull

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')
  {ι κ : Type} (w : ι → A.Pt → Ev n) (w' : κ → A'.Pt → Ev n')

theorem pullback_evalF (f : M' → M) (hf : A.IsHolo A' f) (s : ι → MvPolynomial κ ℝ)
    (hs : ∀ i, A.pullback A' f (fld A (w i)) = evalF A' w' (s i)) (P : MvPolynomial ι ℝ) :
    A.pullback A' f (evalF A w P) = evalF A' w' (aeval s P) := by
  have hp := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf)
  induction P using MvPolynomial.induction_on with
  | C r => rw [evalF_C', aeval_C, algebraMap_eq, evalF_C', (hp.2 (r : ℂ) 1 1).2.2.1, hp.1]
  | add P Q hP hQ => rw [evalF_add', (hp.2 1 _ _).1, hP, hQ, map_add, evalF_add']
  | mul_X P i hP => rw [evalF_mul', (hp.2 1 _ _).2.1, hP, evalF_X', hs, map_mul, aeval_X, evalF_mul']

end Pull

def subQ : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 0, X 3 + X 4 - X 0, X 2, X 3, X 4]

def subB : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 4, X 3, X 2, X 3, X 4]

theorem dvd_aeval_sub (P : MvPolynomial (Fin 5) ℝ) : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ aeval subQ P - aeval subB P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    have hi : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ subQ i - subB i := by
      fin_cases i
      · exact ⟨-1, by simp [subQ, subB]⟩
      · exact ⟨1, by simp [subQ, subB]; ring⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
    rw [map_mul, map_mul, aeval_X, aeval_X,
      show aeval subQ P * subQ i - aeval subB P * subB i =
        (aeval subQ P - aeval subB P) * subQ i + aeval subB P * (subQ i - subB i) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right hi _)

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

theorem evalF_one' {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n) :
    evalF A w 1 = 1 := by
  funext x
  simp [evalF, fld]

theorem logSin_elim : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d →
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * K)) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K _hK
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨hLY, hEY, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hLB, hEB, hPB⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hol, hc1pull, hEpull⟩ := hPB Y p (d + 1) hY π w
  have hrel := (hEpull E h H flB fl).2
  have calcY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have calcB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have lin := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ (d + 1) (hY.atlas σ)
  obtain ⟨hint, hfib⟩ := GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hpl := GlobalTheory.T.flag_bundle_chern_integral_pull_fifth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hglob := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ
  have hpb := calcB.2.2.2.2 _ (d + 1) (hY.atlas σ) _ hol
  set w5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hw5
  let wB : Fin 5 → (hB.atlas σ).Pt → Ev d := ![c1F hB σ (VMetric.grLB flB 1 H), c1F hB σ (VMetric.grLB flB 0 H),
    c1F hB σ A, c1F hB σ (VMetric.grLB flB 0 H), c1F hB σ (VMetric.grLB flB 1 H)]
  have f5 : ∀ i, (hY.atlas σ).IsForm (fld _ (w5 i)) := fun i => (hLY (fam5 π w H flB fl A i) (fam5 π w H flB fl A i)).1.1
  have fB : ∀ i, (hB.atlas σ).IsForm (fld _ (wB i)) := by
    intro i
    fin_cases i
    exacts [(hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1]
  have ev5 : ∀ P, (hY.atlas σ).IsForm (evalF _ w5 P) := fun P => (calcY.2.2.2.1 (Fin 5) w5 P f5).1
  have evB : ∀ P, (hB.atlas σ).IsForm (evalF _ wB P) := fun P => (calcB.2.2.2.1 (Fin 5) wB P fB).1
  have hωY : (hY.atlas σ).IsForm (fld _ (omF hY σ (h.pull π w) fl)) := (hEY _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hωB : (hB.atlas σ).IsForm (fld _ (omF hB σ h flB)) := (hEB E h H flB flB).1.1
  have hmulY : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β → (hY.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcY.2.1 1 α β hα hβ).2.1
  have hmulB : ∀ α β, (hB.atlas σ).IsForm α → (hB.atlas σ).IsForm β → (hB.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcB.2.1 1 α β hα hβ).2.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld _ (omF hB σ h flB))) := ((hpb.2 1 _ 1).2.2.2 hωB).1
  have intAdd : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β →
      (hY.atlas σ).integral (α + β) = (hY.atlas σ).integral α + (hY.atlas σ).integral β := by
    intro α β hα hβ
    rw [← wInt_one, ← wInt_one, ← wInt_one]
    exact (lin.2.1 (fun _ => 1) α β hα hβ (fun ε => by haveI := lin.1 α hα ε; exact integrable_const _)
      (fun ε => by haveI := lin.1 β hβ ε; exact integrable_const _)).2

  have hrel' : ∀ x, w5 1 x = w5 3 x + w5 4 x - w5 0 x := fun x => by
    have e : w5 0 x + w5 1 x = w5 3 x + w5 4 x := congrFun hrel x
    exact eq_sub_of_add_eq' e
  have hsQ : ∀ i, fld _ (w5 i) = evalF (hY.atlas σ) w5 (subQ i) := by
    intro i
    fin_cases i
    · exact (evalF_X' _ w5 0).symm
    · show fld _ (w5 1) = evalF _ w5 (X 3 + X 4 - X 0)
      rw [evalF_sub', evalF_add', evalF_X', evalF_X', evalF_X']
      funext x
      simp only [fld, Pi.add_apply, Pi.sub_apply, hrel' x, AddSubgroupClass.coe_sub, AddMemClass.coe_add]
    · exact (evalF_X' _ w5 2).symm
    · exact (evalF_X' _ w5 3).symm
    · exact (evalF_X' _ w5 4).symm
  have hsB : ∀ i, pullF hB hY σ π w (fld _ (wB i)) = evalF (hY.atlas σ) w5 (subB i) := by
    intro i
    fin_cases i
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull A).symm.trans (evalF_X' _ w5 2).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
  have hφ : pullF hB hY σ π w (evalF _ wB K) = evalF _ w5 (aeval subB K) :=
    pullback_evalF _ _ wB w5 _ hol subB hsB K

  obtain ⟨K1, hK1⟩ := dvd_aeval_sub K
  have hKs : evalF _ w5 K = evalF _ w5 ((X 4 - X 0) * K1) + evalF _ w5 (aeval subB K) := by
    rw [evalF_aeval_self _ w5 subQ hsQ K, ← evalF_add', ← hK1, sub_add_cancel]
  have hXK : evalF _ w5 ((X 0 - X 3) * K) =
      evalF _ w5 ((X 0 - X 3) * ((X 4 - X 0) * K1)) + evalF _ w5 (X 0 - X 3) * pullF hB hY σ π w (evalF _ wB K) := by
    rw [evalF_mul', hKs, mul_add, ← evalF_mul', hφ]

  have e1 := hfib _ (evB K)
  have e2 := (hglob _ (evB K) 0).2
  have e3 := (hglob _ (hmulB _ _ hωB (evB K)) 0).1
  have hs0 : hs 0 = 1 := by simp [hs]
  rw [hs0, map_one, evalF_one', pow_zero, mul_one, one_mul] at e2
  have hpm : ∀ α β, pullF hB hY σ π w (α * β) = pullF hB hY σ π w α * pullF hB hY σ π w β :=
    fun α β => (hpb.2 1 α β).2.1
  rw [pow_zero, one_mul, hpm] at e3
  norm_num at e2
  have hpF : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF _ wB K)) := ((hpb.2 1 _ 1).2.2.2 (evB K)).1
  have eA := (lin.2.1 (fun y => Real.log (1 - v y) / 2) _ _ (ev5 ((X 0 - X 3) * ((X 4 - X 0) * K1)))
    (hmulY _ _ (ev5 (X 0 - X 3)) hpF) (hint _ (ev5 _))
    (hint _ (hmulY _ _ (ev5 (X 0 - X 3)) hpF))).2
  have eK1 := hpl K1
  rw [hXK, eA, eK1, hKs, mul_add, mul_add, intAdd _ _ (hmulY _ _ hωY (ev5 _)) (hmulY _ _ hωY (ev5 _)),
    intAdd _ _ (hmulY _ _ hpω (ev5 _)) (hmulY _ _ hpω (ev5 _)), ← hφ, e1, e2, e3]
  ring

end GlobalTheory.LogSinElim
