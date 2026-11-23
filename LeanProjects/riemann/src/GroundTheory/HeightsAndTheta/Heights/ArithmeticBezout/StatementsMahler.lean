import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

def nrmGroups (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij

def consGroup {k : ℕ} (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) : Fin (k + 1) × Fin n → ℂ :=
  fun ij => Fin.cases (motive := fun _ => ℂ) (v ij.2) (fun i => w (i, ij.2)) ij.1

def IsAdmissible (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : Prop :=
  ∀ W ∈ Z.support, linForm u ∉ W

def mahlerDefect (h : HermNorm n) (e : ℕ) (Z : ProjCycle ℂ n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u)

structure IsChowCycleData (Z : ProjCycle ℂ n) (e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    Prop where

  prime : ∀ W ∈ Z.support, IsProjPrime W

  chow : IsChowFormCycle Z (e + 1) f

  homog : IsMultiHomog δ f

def MahlerSectionDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)

def DefectConstDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u → IsAdmissible Z u' →
      mahlerDefect h e Z f u = mahlerDefect h e Z f u'

def MahlerSectionOfConst.Statement : Prop :=
  ∀ e : ℕ, DefectConstDim e → MahlerSectionDim e

def DefectConstZero.Statement : Prop :=
  DefectConstDim 0

def DefectConstStep.Statement : Prop :=
  ∀ e : ℕ, MahlerSectionDim e → DefectConstDim (e + 1)

def DefectAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) ∧
        ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2

def AdmissibleAE.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) → ∀ᵐ u : Fin n → ℂ, IsAdmissible Z u

def AdmissibleAENrm.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) →
    ∀ᵐ v ∂(volume.restrict (ballH h)), IsAdmissible Z (nrmv h v)

def BallVolume.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n), 0 < volume (ballH h) ∧ volume (ballH h) < ⊤

def MahlerAverageSplit.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun v => mahler h e (specFirst f (nrmv h v))) (ballH h) ∧
      mahler h (e + 1) f = ⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))

def MahlerIntegrand.Statement : Prop :=
  ∀ (n k δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun u => Real.log ‖eval (nrmGroups h k u) f‖) (ballProd h k)

def SphereMeanFubini.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (G : (Fin (k + 1) × Fin n → ℂ) → ℝ),
    IntegrableOn (fun u => G (nrmGroups h (k + 1) u)) (ballProd h (k + 1)) →
      IntegrableOn (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) (ballH h) ∧
        sphereMean h (k + 1) G = ⨍ v in ballH h, sphereMean h k (fun w => G (consGroup (nrmv h v) w))

def EvalSpecFirst.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ),
    eval w (specFirst f v) = eval (consGroup v w) f

def CycleAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => cycleIntegral h Z e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeFubini.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (μ : Measure (EuclideanSpace ℂ (Fin n))) [IsFiniteMeasure μ]
    (F : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) → ℝ) (c M : ℝ),
    Measurable (Function.uncurry F) →
    (∀ᵐ y ∂μ, IntegrableOn (fun v => F v y) (ballH h) ∧ ∫ v in ballH h, |F v y| ≤ M ∧
      ⨍ v in ballH h, F v y = c) →
      IntegrableOn (fun v => ∫ y, F v y ∂μ) (ballH h) ∧
        ⨍ v in ballH h, ∫ y, F v y ∂μ = c * (μ Set.univ).toReal

def FsLogAverage.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
    IntegrableOn (fun v => fsLog h (nrmv h v) (h.pointOf y)) (ballH h) ∧
      ∫ v in ballH h, |fsLog h (nrmv h v) (h.pointOf y)| =
        (harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal ∧
      ⨍ v in ballH h, fsLog h (nrmv h v) (h.pointOf y) = -(harmonic (n - 1) : ℝ) / 2

def FsLogPointOf.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (v : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)),
    fsLog h (nrmv h v) (h.pointOf y) =
      fsLog (HermNorm.std n) (nrmv (HermNorm.std n) (h.mat *ᵥ v)) (fun i => y i)

def BallAverageLinear.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (φ : (Fin n → ℂ) → ℝ),
    (IntegrableOn (fun v => φ (h.mat *ᵥ v)) (ballH h) ↔ IntegrableOn φ (ballH (HermNorm.std n))) ∧
      ⨍ v in ballH h, φ (h.mat *ᵥ v) = ⨍ w in ballH (HermNorm.std n), φ w

def SphereMeanLinearBall.Statement : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℂ), y ≠ 0 →
    IntegrableOn (fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y) (ballH (HermNorm.std n)) ∧
      (∀ w, fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0) ∧
      ⨍ w in ballH (HermNorm.std n), fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y =
        -(harmonic (n - 1) : ℝ) / 2

def FsLogMeasurable.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n),
    Measurable (fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => fsLog h (nrmv h p.1) (h.pointOf p.2))

def ChowDegreePos.Statement : Prop :=
  ∀ (n k δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin k × Fin n) ℂ),
    0 < k → IsProjPrime W → IsChowForm W k g → IsMultiHomog δ g → 1 ≤ δ

def DefectSymm.Statement : Prop :=
  ∀ e : ℕ, MahlerSectionDim e →
    ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ)
      (u u' : Fin n → ℂ), IsChowCycleData Z (e + 1) δ f → IsAdmissible Z u → IsAdmissible Z u' →
      IsAdmissible (cycleSection Z u) u' → IsAdmissible (cycleSection Z u') u →
        mahlerDefect h (e + 1) Z f u = mahlerDefect h (e + 1) Z f u'

def CycleSectionData.Statement : Prop :=
  ∀ (n e δ : ℕ) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsChowCycleData Z (e + 1) δ f → IsAdmissible Z u → IsChowCycleData (cycleSection Z u) e δ (specFirst f u)

def DivCyclePrime.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime W → ∀ W' ∈ (divCycle W u).support, IsProjPrime W'

def SpecFirstHomog.Statement : Prop :=
  ∀ (n k δ : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsMultiHomog δ f → IsMultiHomog δ (specFirst f u)

def SupportCycleSection.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n) (u : Fin n → ℂ),
    (∀ W ∈ Z.support, (divCycle W u).support ⊆ (cycleSection Z u).support) ∧
      ∀ W' ∈ (cycleSection Z u).support, ∃ W ∈ Z.support, W' ∈ (divCycle W u).support

def CycleIntegralSection.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (u : Fin n → ℂ) (e : ℕ) (g : (Fin n → ℂ) → ℝ),
    cycleIntegral h (cycleSection Z u) e g = ∑ W ∈ Z.support, (Z W : ℝ) * cycleIntegral h (divCycle W u) e g

def ChowFormAssoc.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (g g' : MvPolynomial (Fin k × Fin n) F), IsChowForm I k g → IsChowForm I k g' →
      ∃ c : F, c ≠ 0 ∧ g' = C c * g

def ChowFormCycleAdd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z₁ Z₂ : ProjCycle F n) (f₁ f₂ : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z₁ k f₁ → IsChowFormCycle Z₂ k f₂ → IsChowFormCycle (Z₁ + Z₂) k (f₁ * f₂)

def ChowFormCycleSmul.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k m : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → IsChowFormCycle (m • Z) k (f ^ m)

def CycleSectionChow.Statement : Prop :=
  ∀ (n e : ℕ) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsChowFormCycle Z (e + 1) f → IsAdmissible Z u →
      IsChowFormCycle (cycleSection Z u) e (specFirst f u)

def SpecFirstRename.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1 + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
    specFirst (specFirst (rename (Prod.map (Equiv.swap 0 1) id) f) u) u' = specFirst (specFirst f u') u

def ChowCycleSwap.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → ∀ τ : Equiv.Perm (Fin k), ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map τ id) f = C c * f

def SpecFirstSwapMahler.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowFormCycle Z (e + 1 + 1) f →
      mahler h e (specFirst (specFirst f u) u') = mahler h e (specFirst (specFirst f u') u)

def ProperSymm.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ),
    IsProjPrime W → linForm u ∉ W → linForm u' ∉ W → IsAdmissible (divCycle W u) u' →
      IsAdmissible (divCycle W u') u

def ProperSymmCycle.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n) (u u' : Fin n → ℂ),
    (∀ W ∈ Z.support, IsProjPrime W) → IsAdmissible Z u → IsAdmissible Z u' →
      IsAdmissible (cycleSection Z u) u' → IsAdmissible (cycleSection Z u') u

def PointLine.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ),
    IsProjPrime W → IsChowForm W 1 g →
      ∃ y : Fin n → ℂ, y ≠ 0 ∧ (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) ∧
        ∀ q : MvPolynomial (Fin n) ℂ, q ∈ W ↔ ∀ t : ℂ, eval (t • y) q = 0

def PointChowForm.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ) (y : Fin n → ℂ),
    IsChowForm W 1 g → y ≠ 0 → (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) →
      ∃ c : ℂ, c ≠ 0 ∧ g = C c * ∑ j, C (y j) * X ((0 : Fin 1), j)

def ConeIntegralLine.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (y : Fin n → ℂ),
    (∀ x : Fin n → ℂ, (∀ q ∈ W, eval x q = 0) ↔ ∃ t : ℂ, x = t • y) →
    ∀ φ : (Fin n → ℂ) → ℝ, (∀ t : ℂ, t ≠ 0 → φ (t • y) = φ y) →
      coneIntegral h W 0 φ = φ y * coneIntegral h W 0 (fun _ => 1)

def FsLogSmul.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (u y : Fin n → ℂ) (t : ℂ), t ≠ 0 → fsLog h u (t • y) = fsLog h u y

def MahlerZeroSpec.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ),
    mahler h 0 (specFirst f u) = Real.log ‖eval (fun ij => u ij.2) f‖

def DefectPoint.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin 1 × Fin n) ℂ),
    IsProjPrime W → IsChowForm W 1 g → ∃ K : ℝ, ∀ u : Fin n → ℂ, linForm u ∉ W →
      eval (fun ij => u ij.2) g ≠ 0 ∧
        Real.log ‖eval (fun ij => u ij.2) g‖ - coneIntegral h W 0 (fsLog h u) = K

namespace MahlerInhabit

theorem point_data :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) 0 1 (X (0, 0)) := by
  obtain ⟨h1, h2, h3, -⟩ := MahlerSection.hypotheses_inhabited
  exact ⟨h1, h2, h3⟩

theorem point_admissible :
    IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (fun _ => 1) :=
  MahlerSection.hypotheses_inhabited.2.2.2

theorem point_relevant :
    ∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsRelevant W :=
  fun W hW => (MahlerSection.hypotheses_inhabited.1 W hW).isRelevant

theorem point_line :
    ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
      ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) := by
  intro x
  constructor
  · intro _
    exact ⟨x 0, funext fun j => by rw [Fin.fin_one_eq_zero j]; simp⟩
  · rintro - q hq
    rw [Ideal.mem_bot] at hq
    simp [hq]

theorem euclid_ne_zero : (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)) ≠ 0 := by
  intro h0
  have := congrArg (fun y : EuclideanSpace ℂ (Fin 1) => y 0) h0
  simp at this

theorem line_chowCycle :
    IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 2 LineChowForm.D2 := by
  refine ⟨1, one_ne_zero, fun _ => LineChowForm.D2, fun W hW => ?_, ?_⟩
  · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    exact LineChowForm.isChowForm_line
  · rw [Finsupp.support_single _ one_ne_zero]
    simp

theorem line_data :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 := by
  refine ⟨fun W hW => ?_, line_chowCycle, LineChowForm.isMultiHomog_line⟩
  rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
  subst hW
  exact LineChowForm.isProjPrime_line

def coord (a : Fin 2) : Fin 2 → ℂ := fun j => if j = a then 1 else 0

theorem linForm_coord (a : Fin 2) : linForm (coord a) = X a := by
  fin_cases a <;> simp [linForm, coord]

theorem cycleSection_line (u : Fin 2 → ℂ) :
    cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) u = divCycle ⊥ u := by
  simp [cycleSection]

theorem line_proper (a b : Fin 2) (hab : a ≠ b) :
    IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord a)) (coord b) := by
  intro W' hW' hXb
  rw [linForm_coord] at hXb
  have hmem : W' ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ⊔ Ideal.span {linForm (coord a)}) := by
    by_contra hc
    apply Finsupp.mem_support_iff.mp hW'
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    exact if_neg hc
  obtain ⟨hmin, j, hj⟩ := hmem
  have hXa : X a ∈ W' := by
    apply hmin.1.2
    rw [← linForm_coord]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have : j = a ∨ j = b := by fin_cases a <;> fin_cases b <;> fin_cases j <;> simp_all
  rcases this with rfl | rfl
  · exact hj hXa
  · exact hj hXb

theorem line_pair :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0) ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 0)) (coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord 1)) (coord 0) := by
  have hadm : ∀ a : Fin 2, IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (coord a) := by
    intro a W hW
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hW
    subst hW
    rw [linForm_coord, Ideal.mem_bot]
    exact X_ne_zero _
  refine ⟨line_data, hadm 0, hadm 1, ?_, ?_⟩
  · rw [cycleSection_line]; exact line_proper 0 1 (by decide)
  · rw [cycleSection_line]; exact line_proper 1 0 (by decide)

theorem line_prime_pair :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧ linForm (coord 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (coord 1) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord 0)) (coord 1) := by
  refine ⟨LineChowForm.isProjPrime_line, ?_, ?_, line_proper 0 1 (by decide)⟩ <;>
  · rw [linForm_coord, Ideal.mem_bot]; exact X_ne_zero _

end MahlerInhabit

theorem DefectAverage.hypotheses_inhabited :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) 0 1 (X (0, 0)) ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (fun _ => 1) :=
  ⟨MahlerInhabit.point_data, MahlerInhabit.point_admissible⟩

theorem DefectSymm.hypotheses_inhabited :
    IsChowCycleData (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) 1 1 LineChowForm.D2 ∧
      IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 0) ∧ IsAdmissible (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 0)) (MahlerInhabit.coord 1) ∧
      IsAdmissible (cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) (MahlerInhabit.coord 1)) (MahlerInhabit.coord 0) :=
  MahlerInhabit.line_pair

theorem ProperSymm.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (MahlerInhabit.coord 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (MahlerInhabit.coord 1) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (MahlerInhabit.coord 0)) (MahlerInhabit.coord 1) :=
  MahlerInhabit.line_prime_pair

theorem AdmissibleAE.hypotheses_inhabited :
    ∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsRelevant W :=
  MahlerInhabit.point_relevant

theorem FsLogAverage.hypotheses_inhabited :
    (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)) ≠ 0 :=
  MahlerInhabit.euclid_ne_zero

theorem PointChowForm.hypotheses_inhabited :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 (X (0, 0)) ∧ (fun _ : Fin 1 => (1 : ℂ)) ≠ 0 ∧
      ∀ x : Fin 1 → ℂ, (∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)), eval x q = 0) ↔
        ∃ t : ℂ, x = t • (fun _ => (1 : ℂ)) :=
  ⟨isChowForm_point ℂ, fun h0 => one_ne_zero (congrFun h0 0), MahlerInhabit.point_line⟩

theorem ConeFubini.hypotheses_inhabited :
    IsFiniteMeasure (Measure.dirac (0 : EuclideanSpace ℂ (Fin 1))) ∧
      Measurable (Function.uncurry fun (_ : Fin 1 → ℂ) (_ : EuclideanSpace ℂ (Fin 1)) => (0 : ℝ)) :=
  ⟨inferInstance, measurable_const⟩

theorem ChowDegreePos.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧ IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) :=
  ⟨isProjPrime_point ℂ, isChowForm_point ℂ, isMultiHomog_point ℂ⟩

end

end GroundTheory.Heights₂.Heights
