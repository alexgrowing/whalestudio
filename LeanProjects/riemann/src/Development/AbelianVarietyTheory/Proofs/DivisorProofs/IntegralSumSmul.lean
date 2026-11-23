import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingBinomialSumEqPolynomialStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.ChernFibre

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fldA : (A.Pt → Ev n) →ₐ[ℂ] A.Fld :=
  AlgHom.pi fun x => (Subalgebra.center ℂ (Alt n)).val.comp (Pi.evalAlgHom ℂ (fun _ => Ev n) x)

theorem fld_eq (w : A.Pt → Ev n) : fld A w = fldA A w := rfl

theorem evalF_eq {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) :
    evalF A w P = fldA A (aeval w P) := by
  funext x
  have h1 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (f := w) (Pi.evalAlgHom ℂ (fun _ => Ev n) x))
    (P.map (algebraMap ℝ ℂ))
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at h1
  simp only [evalF, fld, fldA, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, Subalgebra.coe_val]
  rw [← h1, MvPolynomial.aeval_map_algebraMap]

theorem aeval_aeval' {S : Type} [CommRing S] [Algebra ℝ S] {ι κ : Type} (f : κ → S) (v : ι → MvPolynomial κ ℝ)
    (P : MvPolynomial ι ℝ) : aeval f (aeval v P) = aeval (fun i => aeval f (v i)) P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

theorem evalF_C {ι : Type} (w : ι → A.Pt → Ev n) (r : ℝ) : evalF A w (C r) = (r : ℂ) • (1 : A.Fld) := by
  rw [evalF_eq, aeval_C, IsScalarTower.algebraMap_apply ℝ ℂ (A.Pt → Ev n), AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]
  rfl

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  simp only [evalF_eq, map_add]

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  simp only [evalF_eq, map_mul]

theorem evalF_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : evalF A w (X i) = fld A (w i) := by
  rw [evalF_eq, aeval_X]; rfl

theorem isForm_pow {α : A.Fld} (h : A.IsForm α) (N : ℕ) : A.IsForm (α ^ N) := by
  induction N with
  | zero => simpa using (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1
  | succ N ih => rw [pow_succ]; exact (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 1 _ _ ih h).2.1)

theorem integral_sum_smul [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    {κ : Type} (S : Finset κ) (r : κ → ℝ) (α : κ → A.Fld) (h : ∀ a ∈ S, A.IsForm (α a)) :
    A.IsForm (∑ a ∈ S, ((r a : ℝ) : ℂ) • α a) ∧
      A.integral (∑ a ∈ S, ((r a : ℝ) : ℂ) • α a) = ∑ a ∈ S, r a * A.integral (α a) := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have F := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  have hint : ∀ β : A.Fld, A.IsForm β → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part β ε) := by
    intro β hβ ε
    haveI := L.1 β hβ ε
    exact integrable_const _
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (F.2.1 0 1 1 F.1 F.1).2.2.1, ?_⟩
    have h0 := L.2.2.1 (fun _ => 1) 0 1 F.1
    simp only [Complex.ofReal_zero, zero_smul, zero_mul, wInt_one] at h0
    simpa using h0
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    have hs : A.IsForm (((r a : ℝ) : ℂ) • α a) := (F.2.1 _ (α a) (α a) (h a (Finset.mem_insert_self a S))
      (h a (Finset.mem_insert_self a S))).2.2.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨(F.2.1 1 _ _ hs ih1).1, ?_⟩
    have e := (L.2.1 (fun _ => 1) _ _ hs ih1 (hint _ hs) (hint _ ih1)).2
    rw [wInt_one, wInt_one, wInt_one] at e
    rw [e, ih2]
    have e2 := L.2.2.1 (fun _ => 1) (r a) (α a) (h a (Finset.mem_insert_self a S))
    rw [wInt_one, wInt_one] at e2
    rw [e2]

end Manifold

theorem pullback_evalF {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f) {ι : Type} (w : ι → A.Pt → Ev n)
    (w' : ι → A'.Pt → Ev n') (hw : ∀ i, A.pullback A' f (fld A (w i)) = fld A' (w' i)) (P : MvPolynomial ι ℝ) :
    A.pullback A' f (evalF A w P) = evalF A' w' P := by
  have F := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf)
  induction P using MvPolynomial.induction_on with
  | C r => rw [evalF_C, evalF_C, (F.2 _ 1 1).2.2.1, F.1]
  | add P Q hP hQ => rw [evalF_add, evalF_add, (F.2 1 _ _).1, hP, hQ]
  | mul_X P i hP => rw [evalF_mul, evalF_mul, evalF_X, evalF_X, (F.2 1 _ _).2.1, hP, hw]

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem expand_line {R : Type} [CommRing R] [Algebra ℂ R] (ω θ c V : R) (hω : ω * ω = 0) (M : ℕ) :
    ω * (θ * (c - θ)) ^ M * V = ∑ j ∈ Finset.range (M + 1),
      (((-1) ^ j * (M.choose j : ℝ) : ℝ) : ℂ) • (ω * (θ + ω) ^ (M + j) * (c ^ (M - j) * V)) := by
  have hp : ∀ N : ℕ, ω * (θ + ω) ^ N = ω * θ ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_add]
      have e2 : ω * θ ^ N * ω = θ ^ N * (ω * ω) := by ring
      rw [e2, hω]
      ring
  have e : c - θ = -θ + c := by ring
  rw [mul_pow, e, add_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hp, Algebra.smul_def]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast,
    map_mul, map_pow, map_neg, map_one, map_natCast, neg_pow θ]
  ring

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem evalF_sum_C_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι κ : Type} (w : ι → A.Pt → Ev n)
    (S : Finset κ) (r : κ → ℝ) (P : κ → MvPolynomial ι ℝ) :
    evalF A w (∑ a ∈ S, C (r a) * P a) = ∑ a ∈ S, ((r a : ℝ) : ℂ) • evalF A w (P a) := by
  rw [evalF_eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, aeval_C, map_mul, evalF_eq, IsScalarTower.algebraMap_apply ℝ ℂ (A.Pt → Ev n), AlgHom.commutes,
    ← Algebra.smul_def]
  rfl

theorem downP_expand {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) :
    downP s m W = ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), C ((-1) ^ j * ((m i).choose j : ℝ) / ((m i : ℝ) + j + 1)) *
      (aeval ![X 1 + X 2, X 3] (hs (m i + j)) * ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i))) := by
  unfold downP
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← GlobalTheory.T.alternating_binomial_sum_eq_polynomial (m i)]
  simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X, Finset.sum_mul, MvPolynomial.algebraMap_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.cons_val_zero]
  ring

end GlobalTheory.LineForm.ChernFibre

namespace GlobalTheory.LineForm.ChernFibre

theorem fibre_integral_eq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (downP s m W)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ ι s m W
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hB.isProjOver
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  have I5B := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have I5Y := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have FB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have FY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have hol := (I5B.2.2 Y p (d + 1) hY π w).1
  set x : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx
  set ω := omF hY σ (h.pull π w) fl with hω
  set f4 := fam4 hB σ H flB A with hf4
  set g4 : Fin 4 → (hY.atlas σ).Pt → Ev (d + 1) := ![x 2, x 3, x 4, c2F hY σ (h.pull π w) fl] with hg4
  set φ : ι → ℕ → (hB.atlas σ).Fld := fun i j =>
    evalF (hB.atlas σ) f4 ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i)) with hφ
  set T : ι → ℕ → (hY.atlas σ).Fld := fun i j =>
    fld _ ω * (fld _ (x 0) + fld _ ω) ^ (m i + j) * pullF hB hY σ π w (φ i j) with hT
  set U : ι → ℕ → (hB.atlas σ).Fld := fun i j =>
    evalF (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m i + j))) * φ i j with hU
  set cf : ι → ℕ → ℝ := fun i j => (-1) ^ j * ((m i).choose j : ℝ) with hcf

  have hpull4 : ∀ i, (hB.atlas σ).pullback (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) (fld _ (f4 i)) = fld _ (g4 i) := by
    intro i
    fin_cases i
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 A).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 (VMetric.grLB flB 0 H)).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.1 (VMetric.grLB flB 1 H)).symm
    · exact ((I5B.2.2 Y p (d + 1) hY π w).2.2 E h H flB fl).1.symm

  have hf4F : ∀ i, (hB.atlas σ).IsForm (fld _ (f4 i)) := by
    intro i
    fin_cases i
    · exact (I5B.1 A A).1.1
    · exact (I5B.1 (VMetric.grLB flB 0 H) A).1.1
    · exact (I5B.1 (VMetric.grLB flB 1 H) A).1.1
    · exact (I5B.2.1 E h H flB flB).2.1.1
  have hevB : ∀ P : MvPolynomial (Fin 4) ℝ, (hB.atlas σ).IsForm (evalF (hB.atlas σ) f4 P) :=
    fun P => (FB.2.2.2.1 _ f4 P hf4F).1
  have hφF : ∀ i j, (hB.atlas σ).IsForm (φ i j) := fun i j => hevB _
  have hUF : ∀ i j, (hB.atlas σ).IsForm (U i j) := fun i j => (FB.2.1 1 _ _ (hevB _) (hφF i j)).2.1
  have hωF : (hY.atlas σ).IsForm (fld _ ω) := (I5Y.2.1 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hθF : (hY.atlas σ).IsForm (fld _ (x 0)) := (I5Y.1 _ (fam5 π w H flB fl A 0)).1.1
  have hωω : ω * ω = 0 := (I5Y.2.1 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1
  have hTF : ∀ i j, (hY.atlas σ).IsForm (T i j) := by
    intro i j
    have hpF := (((FB.2.2.2.2 _ _ _ _ hol).2 1 (φ i j) (φ i j)).2.2.2 (hφF i j)).1
    exact (FY.2.1 1 _ _ (FY.2.1 1 _ _ hωF (isForm_pow _ (FY.2.1 1 _ _ hθF hωF).1 _)).2.1 hpF).2.1

  have hpT : ∀ i j, pullF hB hY σ π w (φ i j) =
      fldA _ ((x 3 + x 4) ^ (m i - j) * aeval ![x 2, x 3, x 4] (W i)) := by
    intro i j
    refine (pullback_evalF _ _ _ hol f4 g4 hpull4 ((X 1 + X 2) ^ (m i - j) * aeval ![X 0, X 1, X 2] (W i))).trans ?_
    rw [evalF_eq]
    congr 1
    simp only [map_mul, map_pow, map_add, aeval_X]
    rw [aeval_aeval']
    have e : (fun t : Fin 3 => aeval g4 ((![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 4) ℝ) t)) =
        ![x 2, x 3, x 4] := by
      funext t; fin_cases t <;> simp [g4]
    rw [e]
    rfl
  have hT' : ∀ i j, T i j =
      fldA _ (ω * (x 0 + ω) ^ (m i + j) * ((x 3 + x 4) ^ (m i - j) * aeval ![x 2, x 3, x 4] (W i))) := by
    intro i j
    simp only [hT, hpT, fld_eq, map_mul, map_pow, map_add]
  have hup : aeval x (upperParabolic s m W) = ∑ i ∈ s, (x 0 * (x 3 + x 4 - x 0)) ^ m i * aeval ![x 2, x 3, x 4] (W i) := by
    simp only [upperParabolic, map_sum, map_mul, map_pow, map_add, map_sub, aeval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_aeval']
    have e : (fun t : Fin 3 => aeval x ((![X 2, X 3, X 4] : Fin 3 → MvPolynomial (Fin 5) ℝ) t)) =
        ![x 2, x 3, x 4] := by
      funext t; fin_cases t <;> simp
    rw [e]
  have hY1 : fld _ ω * evalF _ x (upperParabolic s m W) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), ((cf i j : ℝ) : ℂ) • T i j := by
    rw [evalF_eq, fld_eq, ← map_mul, hup, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    refine (congrArg (fldA (hY.atlas σ)) (expand_line ω (x 0) (x 3 + x 4) (aeval ![x 2, x 3, x 4] (W i)) hωω (m i))).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hT']
  have hIY : (hY.atlas σ).integral (fld _ ω * evalF _ x (upperParabolic s m W)) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), cf i j * (hY.atlas σ).integral (T i j) := by
    rw [hY1, Finset.sum_sigma', Finset.sum_sigma']
    exact (integral_sum_smul (hY.atlas σ) (s.sigma fun i => Finset.range (m i + 1)) (fun a => cf a.1 a.2)
      (fun a => T a.1 a.2) fun a _ => hTF a.1 a.2).2

  have hB1 : evalF _ f4 (downP s m W) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), ((cf i j / ((m i : ℝ) + j + 1) : ℝ) : ℂ) • U i j := by
    rw [downP_expand, Finset.sum_sigma', Finset.sum_sigma', evalF_sum_C_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [evalF_mul]
  have hIB : (hB.atlas σ).integral (evalF _ f4 (downP s m W)) =
      ∑ i ∈ s, ∑ j ∈ Finset.range (m i + 1), cf i j / ((m i : ℝ) + j + 1) * (hB.atlas σ).integral (U i j) := by
    rw [hB1, Finset.sum_sigma', Finset.sum_sigma']
    exact (integral_sum_smul (hB.atlas σ) (s.sigma fun i => Finset.range (m i + 1))
      (fun a => cf a.1 a.2 / ((m a.1 : ℝ) + a.2 + 1)) (fun a => U a.1 a.2) fun a _ => hUF a.1 a.2).2
  have hTU : ∀ i j, (hY.atlas σ).integral (T i j) = 1 / (((m i + j : ℕ) : ℝ) + 1) * (hB.atlas σ).integral (U i j) :=
    fun i j => (GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ (φ i j) (hφF i j) (m i + j)).2
  rw [hIY, hIB]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hTU]
  push_cast
  ring

end GlobalTheory.LineForm.ChernFibre
