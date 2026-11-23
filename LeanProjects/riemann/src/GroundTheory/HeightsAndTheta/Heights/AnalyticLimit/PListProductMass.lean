import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PDivisorNull
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListProductMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

theorem isPsh_add_neg {A : FinHolAtlas D X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hP : IsPotential A P) (hle : LeviLe A Set.univ 1 P 1 Q) : IsPsh A (Q + P.rsmul (-1)) := by
  intro x j y hy w
  have hyQ : (A.chart j).symm y ∈ Q.U x := hy.2.1
  have hyP : (A.chart j).symm y ∈ P.U x := hy.2.2
  have hlev := hle x j y ⟨hy.1, ⟨⟨Set.mem_univ _, hyP⟩, hyQ⟩⟩ w
  have hadd := levi_add_smul (-1) (pot_contDiffAt_two hQ x j hy.1 hyQ)
    (pot_contDiffAt_two hP x j hy.1 hyP) w
  show 0 ≤ levi (fun z => (Q.φ x ∘ (A.chart j).symm) z + (-1) * (P.φ x ∘ (A.chart j).symm) z) y w
  rw [hadd]
  linarith

theorem mInt_congr_φ (A : FinHolAtlas D X) {Φ Ψ : Fin D → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt ReciprocityTheory.AnForm.M.integralWith ReciprocityTheory.AnForm.M.locDens
  simp only [h]

theorem ListProductMass.proof : ListProductMass.Statement := by
  intro D X _ _ _ A R Om C₁ th u hT
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hNull := (DivisorNull.proof A R).2
  let T : Fin D → LocPot X := fun i => potForm (th i) (u i)
  let Q : Fin D → LocPot X := fun i => Om.pot + (th i).rsmul (-1)
  have hTpot : ∀ i, IsPotential A (T i) := fun i =>
    isPotentialAdd A _ _ (hT i).1.th_pot (isPotential_ofFun A _ (hT i).2)
  have hTpsh : ∀ i, IsPsh A (T i) := fun i => isPsh_of_formNonneg hNull (hTpot i) (hT i).1.nonneg
  have hQpot : ∀ i, IsPotential A (Q i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotentialRsmul A _ _ (hT i).1.th_pot)
  have hQpsh : ∀ i, IsPsh A (Q i) := fun i => isPsh_add_neg Om.isPot (hT i).1.th_pot (hT i).1.th_le
  have hSpot : ∀ i, IsPotential A (T i + Q i) := fun i => isPotentialAdd A _ _ (hTpot i) (hQpot i)
  have hSpsh : ∀ i, IsPsh A (T i + Q i) := fun i =>
    isPshAdd A _ _ (hTpot i) (hQpot i) (hTpsh i) (hQpsh i)
  have hmono := maMeasureMono A T Q hTpot hTpsh hQpot hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A T hTpot hTpsh
  obtain ⟨hfinS, hS'⟩ := maMeasure_thm A (fun i => T i + Q i) hSpot hSpsh
  have e1 : mInt A T (fun _ => 1) = (maMeasure A T).real Set.univ := by
    rw [(hT' _ measurable_const).2 (mIntegrableCont A T hTpot _ continuous_const), integral_const,
      smul_eq_mul, mul_one]
  have e2 : mInt A (fun i => T i + Q i) (fun _ => 1) =
      (maMeasure A (fun i => T i + Q i)).real Set.univ := by
    rw [(hS' _ measurable_const).2 (mIntegrableCont A _ hSpot _ continuous_const), integral_const,
      smul_eq_mul, mul_one]
  have e3 : mInt A (fun i => T i + Q i) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + (Om.pot.φ x y + -1 * (th i).φ x y) = Om.pot.φ x y + u i y
    ring
  have e4 : mInt A (fun i => Om.pot + LocPot.ofFun (u i)) (fun _ => 1) = Om.vol :=
    massIndep A (fun _ => Om.pot) u (fun _ => Om.isPot) (fun i => (hT i).2)
  have hle : (maMeasure A T).real Set.univ ≤ (maMeasure A (fun i => T i + Q i)).real Set.univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 hmono Set.univ)
  change mInt A T (fun _ => 1) ≤ Om.vol
  rw [e1, ← e4, ← e3, e2]
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
