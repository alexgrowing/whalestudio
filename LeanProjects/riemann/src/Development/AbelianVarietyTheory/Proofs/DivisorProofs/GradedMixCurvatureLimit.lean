import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.CurvJet

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {j k : WithTop ℕ∞} {m : ℕ}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem contDiffAt_partial {f : ℝ × E → ℂ} {p : ℝ × E} (h : ContDiffAt ℝ k f p)
    (hjk : j + 1 ≤ k) :
    ContDiffAt ℝ j (fun q : ℝ × E => fderiv ℝ (fun x => f (q.1, x)) q.2) p := by
  refine ContDiffAt.fderiv (f := fun (q : ℝ × E) (x : E) => f (q.1, x)) (g := Prod.snd) ?_
    contDiffAt_snd hjk
  exact ContDiffAt.comp (g := f) (f := fun r : (ℝ × E) × E => (r.1.1, r.2)) (p, p.2) h
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)

theorem mContDiffAt_mdel {A : ℝ × E → Matrix (Fin m) (Fin m) ℂ} {p : ℝ × E}
    (h : MContDiffAt k A p) (hjk : j + 1 ≤ k) (ξ : E) :
    MContDiffAt j (fun q : ℝ × E => mdel (fun x => A (q.1, x)) q.2 ξ) p := fun a b => by
  have h1 := contDiffAt_partial (h a b) hjk
  simp only [mdel_apply, del_apply]
  exact ((h1.clm_apply contDiffAt_const).sub
    ((h1.clm_apply contDiffAt_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem mContDiffAt_mdbar {A : ℝ × E → Matrix (Fin m) (Fin m) ℂ} {p : ℝ × E}
    (h : MContDiffAt k A p) (hjk : j + 1 ≤ k) (ξ : E) :
    MContDiffAt j (fun q : ℝ × E => mdbar (fun x => A (q.1, x)) q.2 ξ) p := fun a b => by
  have h1 := contDiffAt_partial (h a b) hjk
  simp only [mdbar_apply, dbar_apply]
  exact ((h1.clm_apply contDiffAt_const).add
    ((h1.clm_apply contDiffAt_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem tendsto_curv {A : ℝ × E → Matrix (Fin m) (Fin m) ℂ} {c₀ : ℝ} {u : E}
    (h : MContDiffAt 2 A (c₀, u)) (hu : IsUnit (A (c₀, u)).det) (ξ η : E) :
    Tendsto (fun c : ℝ => curv (fun x => A (c, x)) u ξ η) (𝓝 c₀)
      (𝓝 (curv (fun x => A (c₀, x)) u ξ η)) := by
  have h1 : MContDiffAt 1 (fun q : ℝ × E => conn (fun x => A (q.1, x)) q.2 ξ) (c₀, u) :=
    ((h.of_le one_le_two).transpose.inv (by rwa [det_transpose])).mul
      (mContDiffAt_mdel h (by norm_num) ξ).transpose
  have h2 : MContDiffAt 0 (fun q : ℝ × E => curv (fun x => A (q.1, x)) q.2 ξ η) (c₀, u) :=
    (mContDiffAt_mdbar h1 (by norm_num) η).neg
  refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
  exact ContinuousAt.comp (f := fun c : ℝ => (c, u)) (h2 a b).continuousAt
    (continuousAt_id.prodMk continuousAt_const)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem mContDiffAt_mix {A B : E → Matrix (Fin m) (Fin m) ℂ} {ρ : E → ℝ} {u : E}
    (hA : MContDiffAt 2 A u) (hB : MContDiffAt 2 B u) (hρ : ContDiffAt ℝ 2 ρ u) :
    MContDiffAt 2 (fun q : ℝ × E => GlobalTheory.GradedNorm.mix (1 / (1 + q.1 * ρ q.2)) (A q.2) (B q.2))
      (0, u) := by
  have hs : ContDiffAt ℝ 2 (fun q : ℝ × E => 1 / (1 + q.1 * ρ q.2)) (0, u) :=
    contDiffAt_const.div (contDiffAt_const.add (contDiffAt_fst.mul
      (ContDiffAt.comp (g := ρ) (f := Prod.snd) (0, u) hρ contDiffAt_snd))) (by simp)
  have hA' : MContDiffAt 2 (fun q : ℝ × E => A q.2) (0, u) := fun a b =>
    ContDiffAt.comp (g := fun x => A x a b) (f := Prod.snd) (0, u) (hA a b) contDiffAt_snd
  have hB' : MContDiffAt 2 (fun q : ℝ × E => B q.2) (0, u) := fun a b =>
    ContDiffAt.comp (g := fun x => B x a b) (f := Prod.snd) (0, u) (hB a b) contDiffAt_snd
  have hc : ContDiffAt ℝ 2 (fun q : ℝ × E => ((1 / (1 + q.1 * ρ q.2) : ℝ) : ℂ)) (0, u) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hs
  have hc' : ContDiffAt ℝ 2 (fun q : ℝ × E => ((1 - 1 / (1 + q.1 * ρ q.2) : ℝ) : ℂ)) (0, u) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_const.sub hs)
  unfold GlobalTheory.GradedNorm.mix
  exact (MContDiffAt.smul hc' hA').add (MContDiffAt.smul hc hB')

end Param

theorem mix_zero {m : ℕ} (r : ℝ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.GradedNorm.mix (1 / (1 + 0 * r)) A B = B := by
  simp [GlobalTheory.GradedNorm.mix]

theorem dualGram_dualGram {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (h : IsUnit A.det) :
    GlobalTheory.HermFrame.dualGram (GlobalTheory.HermFrame.dualGram A) = A := by
  rw [GlobalTheory.HermFrame.dualGram, GlobalTheory.HermFrame.dualGram, ← transpose_nonsing_inv,
    transpose_transpose, nonsing_inv_nonsing_inv _ h]

theorem tendsto_curv_mix : ∀ {n m : ℕ} (H₀ H : V n → Matrix (Fin m) (Fin m) ℂ) (ρ : V n → ℝ) (u : V n),
    (∀ i k, ContDiffAt ℝ 2 (fun v => H₀ v i k) u) → (∀ i k, ContDiffAt ℝ 2 (fun v => H v i k) u) →
    ContDiffAt ℝ 2 ρ u → IsUnit (H₀ u).det → IsUnit (H u).det → ∀ ξ η : V n,
    Tendsto (fun c : ℝ => curv (fun v => GlobalTheory.GradedNorm.mix (1 / (1 + c * ρ v)) (H₀ v) (H v)) u ξ η) (𝓝 0)
        (𝓝 (curv H u ξ η)) ∧
      Tendsto (fun c : ℝ => curv (fun v => GlobalTheory.HermFrame.dualGram (GlobalTheory.GradedNorm.mix (1 / (1 + c * ρ v))
        (GlobalTheory.HermFrame.dualGram (H₀ v)) (GlobalTheory.HermFrame.dualGram (H v)))) u ξ η) (𝓝 0) (𝓝 (curv H u ξ η)) := by
  intro n m H₀ H ρ u h0 h1 hρ u0 u1 ξ η
  have h0' : MContDiffAt 2 H₀ u := h0
  have h1' : MContDiffAt 2 H u := h1
  constructor
  · have := tendsto_curv (mContDiffAt_mix h0' h1' hρ) (by simpa only [mix_zero] using u1) ξ η
    simpa only [mix_zero] using this
  · have hm := mContDiffAt_mix (A := fun v => GlobalTheory.HermFrame.dualGram (H₀ v))
      (B := fun v => GlobalTheory.HermFrame.dualGram (H v)) (h0'.inv u0).transpose (h1'.inv u1).transpose hρ
    have hd : IsUnit (GlobalTheory.HermFrame.dualGram (H u)).det := by
      rw [GlobalTheory.HermFrame.dualGram, det_transpose]; exact isUnit_nonsing_inv_det _ u1
    have := tendsto_curv (A := fun q : ℝ × V n => GlobalTheory.HermFrame.dualGram
        (GlobalTheory.GradedNorm.mix (1 / (1 + q.1 * ρ q.2))
        (GlobalTheory.HermFrame.dualGram (H₀ q.2)) (GlobalTheory.HermFrame.dualGram (H q.2))))
      (hm.inv (by simpa only [mix_zero] using hd)).transpose
      (by simpa only [mix_zero, dualGram_dualGram u1] using u1) ξ η
    simp only [mix_zero] at this
    rwa [curv_congr (H' := H) ((h1'.eventually_isUnit u1).mono fun x hx => dualGram_dualGram hx)]
      at this

end GlobalTheory.CurvJet
