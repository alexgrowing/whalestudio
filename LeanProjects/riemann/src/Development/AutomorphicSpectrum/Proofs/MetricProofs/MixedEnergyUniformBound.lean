import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.TailBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLogSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LemmaETailMass
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit

theorem tailLogBound_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hd : ∀ j y, ReciprocityTheory.AnForm.M.locDens A Φ j y = ReciprocityTheory.AnForm.M.locDens A Ψ j y := by
    intro j y
    simp only [ReciprocityTheory.AnForm.M.locDens, h]
  have hM : ∀ g, ReciprocityTheory.AnForm.M.MIntegrable A Φ g ↔ ReciprocityTheory.AnForm.M.MIntegrable A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.MIntegrable, hd]
  have hI : ∀ g, ReciprocityTheory.AnForm.M.mInt A Φ g = ReciprocityTheory.AnForm.M.mInt A Ψ g := by
    intro g
    simp only [ReciprocityTheory.AnForm.M.mInt, ReciprocityTheory.AnForm.M.integralWith, hd]
  intro R₀ hR
  rw [← hM, ← hI]
  exact H R₀ hR

theorem tailLogProducts : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  intro e X _ _ _ A R Θ hΘ hΘp P C hP
  have hSmooth : ListTailLogSmooth.Statement :=
    ListTailLogSmooth.proof
      (GroundTheory.Heights₂.Heights.ForSecondHalf.ListTailLog.of_lemmaETailMass lemmaETailMass)
  let R₁ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.RegChartData.ofRegular R Θ hΘ hΘp
  let R' := regChartShift R₁
  have hconst : A.Smooth (fun _ : X => C) := fun j => contDiffOn_const
  let th : Fin e → LocPot X := fun i => P i + LocPot.ofFun (fun _ => C)
  have hth : ∀ i, IsPotential A (th i) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ hconst)
  obtain ⟨Om, hOm⟩ := BoundingKaehler.full e A ⟨Θ, hΘ, hΘp⟩ e th hth
  obtain ⟨CE, hCE⟩ := hSmooth A R' Om (3 * |C|)
  refine ⟨CE, fun f hf hpsh habs hle => ?_⟩
  let u : Fin e → X → ℝ := fun i x => f i x - C
  have hu : ∀ i, A.Smooth (u i) := fun i j => (hf i j).sub contDiffOn_const
  have hφ : ∀ i, (potForm (th i) (u i)).φ = (P i + LocPot.ofFun (f i)).φ := by
    intro i
    funext x y
    show (P i).φ x y + C + (f i y - C) = (P i).φ x y + f i y
    ring
  have hnn : ∀ i, FormNonneg A R.Yo (P i + LocPot.ofFun (f i)) := fun i x k y hy w =>
    hpsh i x k y ⟨hy.1, hy.2.2⟩ w
  have hform : ∀ i, IsSmoothPotForm A R'.Yo R'.r Om (3 * |C|) (th i) (u i) := by
    intro i
    refine ⟨⟨hth i, (hOm i).1, (hOm i).2, ?_, ?_, ?_, ?_, Or.inl (hu i)⟩, hu i⟩
    · exact fun j => (hu i j).mono fun y hy => ⟨hy.1, trivial⟩
    · intro x hx
      have := hle i x hx
      show f i x - C ≤ 0
      linarith
    · intro x hx
      have hx' : x ∈ R.Yo := hx
      have h1 : 1 ≤ R.r x := R.one_le_r x hx'
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hL : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have hL1 : 1 ≤ Real.log (R.r x + (Real.exp 1 - 1)) := by
        have h2 : Real.log (Real.exp 1) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
          Real.log_le_log (Real.exp_pos 1) (by linarith)
        rwa [Real.log_exp] at h2
      have hL0 := Real.log_nonneg h1
      have hf' : -(C + C * Real.log (R.r x)) ≤ f i x := by
        have := (neg_abs_le (f i x))
        linarith [habs i x hx']
      have hc1 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        mul_le_mul (le_abs_self C) hL hL0 (abs_nonneg C)
      have hc2 : |C| ≤ |C| * Real.log (R.r x + (Real.exp 1 - 1)) :=
        le_mul_of_one_le_right (abs_nonneg _) hL1
      have hc3 := le_abs_self C
      show -(3 * |C| * Real.log (R.r x + (Real.exp 1 - 1))) ≤ f i x - C
      linarith
    · intro x k y hy w
      have := hnn i x k y ⟨hy.1, hy.2.1, hy.2.2.1⟩ w
      rw [hφ i]
      exact this
  have hB := hCE th u hform
  have hpot : ∀ i, IsPotential A (P i + LocPot.ofFun (f i)) := fun i =>
    isPotentialAdd A _ _ (hP i) (isPotential_ofFun A _ (hf i))
  have hB' : TailLogBound A R.Yo R'.r (fun i => P i + LocPot.ofFun (f i)) CE :=
    tailLogBound_of_φ_eq A _ _ hφ CE hB
  exact tailLogBound_of_le (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.isOpen_Yo_regular R)
    (regChartData_continuousOn_r R₁) (r' := R'.r)
    (fun x _ => by
      show R.r x ≤ R.r x + (Real.exp 1 - 1)
      linarith [Real.add_one_le_exp (1 : ℝ)])
    hpot hnn hB'

end GlobalTheory.CompanionTheory.Ar.Giv
