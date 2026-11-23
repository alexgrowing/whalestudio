import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.WordTens
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchInf
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic

open MeasureTheory MeasureTheory.Measure NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo

private theorem UpperTheory.ConvolutionTheory.L1.pairPosition_cv {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (ν : Measure H)
    (a b : H → ℂ) (x : G) :
    UpperTheory.ConvolutionTheory.L1.cv (ν.map e.symm) (fun g => a (e g)) (fun g => b (e g)) x = UpperTheory.ConvolutionTheory.L1.cv ν a b (e x) := by
  have hemb : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  unfold UpperTheory.ConvolutionTheory.L1.cv
  rw [hemb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [map_mul, map_inv]

private theorem UpperTheory.ConvolutionTheory.L1.pairPosition_cvAll {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (ν : Measure H) (m : ℕ)
    (φ : Fin (m + 1) → H → ℂ) :
    UpperTheory.ConvolutionTheory.L1.cvAll (ν.map e.symm) m (fun i g => φ i (e g)) = fun g => UpperTheory.ConvolutionTheory.L1.cvAll ν m φ (e g) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext g
    have h := ih (Fin.tail φ)
    simp only [UpperTheory.ConvolutionTheory.L1.cvAll]
    have ht : (Fin.tail fun i g => φ i (e g)) = fun i g => Fin.tail φ i (e g) := rfl
    rw [ht, h]
    exact UpperTheory.ConvolutionTheory.L1.pairPosition_cv e ν _ _ g

private theorem UpperTheory.ConvolutionTheory.L1.pairPosition_one {X : Type} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsHaarMeasure] (c : ℝ)
    (h : μ = ENNReal.ofReal c • μ) : c = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : X)
  have h0 : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hK1).ne'
  have ht : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 : μ K = ENNReal.ofReal c * μ K := by
    conv_lhs => rw [h]
    simp
  have h2 : ENNReal.ofReal c = 1 := by
    have h3 : ENNReal.ofReal c * μ K = 1 * μ K := by rw [one_mul]; exact h1.symm
    exact (ENNReal.mul_left_inj h0 ht).1 h3
  exact ENNReal.ofReal_eq_one.1 h2

theorem UpperTheory.ConvolutionTheory.L1.pairPosition :
    UpperTheory.ConvolutionTheory.L1.PairPosition := by
  intro F E _ _ _ _ _ _ _ σ m hm D n νE _ νF _ b a aE aF hS mE bE mF bF w
  obtain ⟨φ, hT, hC⟩ := UpperTheory.ConvolutionTheory.L1.wordTens F E σ m D n νE νF b a aE aF hS w
  obtain ⟨-, -, -, hglueA, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  obtain ⟨-, -, -, hglue, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ m D n
  haveI : SecondCountableTopology (GL (Fin n) (InfiniteAdeleRing F)) :=
    (archEquiv F n).toHomeomorph.secondCountableTopology
  haveI : IsHaarMeasure (νE.map (archEquiv E n).symm) :=
    (archEquiv E n).symm.isHaarMeasure_map νE
  haveI : IsHaarMeasure (νF.map (archEquiv F n).symm) :=
    (archEquiv F n).symm.isHaarMeasure_map νF
  obtain ⟨c, hc, hμ, hM, hTn⟩ := UpperTheory.ConvolutionTheory.L1.matchInf F E σ m D n (νE.map (archEquiv E n).symm)
    (νF.map (archEquiv F n).symm) inferInstance inferInstance
  have hmeas : νE.map (archEquiv E n).symm =
      Measure.map (D.glue n) (Measure.pi fun _ => νF.map (archEquiv F n).symm) := by
    have hsymm : Continuous fun g : Fin (m + 1) → archGroup F n => fun i => (archEquiv F n).symm (g i) :=
      continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)
    have hEs : Measurable (archEquiv E n).symm := (archEquiv E n).symm.continuous.measurable
    have hFs : Measurable (archEquiv F n).symm := (archEquiv F n).symm.continuous.measurable
    rw [hS.meas, Measure.map_map hEs hglueA.measurable,
      ← Measure.pi_map_pi (fun _ => hFs.aemeasurable),
      Measure.map_map hglue.measurable hsymm.measurable]
    congr 1
    funext g
    simp [UpperTheory.ConvolutionTheory.L1.glueA]
  have hc1 : c = 1 := by
    refine UpperTheory.ConvolutionTheory.L1.pairPosition_one (νE.map (archEquiv E n).symm) c ?_
    have h := hμ
    rw [← hmeas] at h
    exact h
  have hφ : ∀ i, Continuous (GM.onInf (φ i)) ∧ HasCompactSupport (GM.onInf (φ i)) := fun i =>
    ⟨(φ i).continuous.comp (archEquiv F n).continuous,
      (φ i).hasCompactSupport.comp_homeomorph (archEquiv F n).toHomeomorph⟩
  obtain ⟨h1c, h2c, h3c⟩ := hTn (fun i => GM.onInf (φ i)) hφ
  have h1 : GM.onInf (GM.word νE aE w) = D.tens n fun i => GM.onInf (φ i) := by
    funext g
    refine (hT _).trans (Finset.prod_congr rfl fun i _ => ?_)
    have hg : (archEquiv E n).symm (archEquiv E n g) = g := by simp
    change (φ i) ((archEquiv F n) (D.comp n i ((archEquiv E n).symm (archEquiv E n g)))) =
      (φ i) ((archEquiv F n) (D.comp n i g))
    rw [hg]
  have h2 : GM.onInf (GM.word νF aF (w.map (GM.resIx F))) = D.transfer n (νF.map (archEquiv F n).symm)
      (D.tens n fun i => GM.onInf (φ i)) := by
    rw [h3c]
    have := UpperTheory.ConvolutionTheory.L1.pairPosition_cvAll (archEquiv F n) νF m (fun i => φ i)
    refine Eq.trans ?_ this.symm
    funext g
    exact hC _
  rw [hm, h1, h2]
  have := hM _ h1c h2c
  rw [hc1] at this
  exact this
