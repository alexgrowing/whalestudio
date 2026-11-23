import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open scoped ContDiff

namespace GlobalTheory.Mean4O.ReadsProj

theorem hess_comb : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (σ : k →+* ℂ) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}, y ∈ c.e.source → ∀ (i : (ArInt.comb L n).B.ι), y ∈ ptsIn p σ ((ArInt.comb L n).B.U i) → ∀ (m : ∀ l, (L l).B.ι), (∀ l, y ∈ ptsIn p σ ((L l).B.U (m l))) → c.hess ((ArInt.comb L n).φ σ) i y = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y := by
  classical
  intro k _ X p ι _ L n σ D c y hy i hi m hm
  obtain ⟨i₀, hi₀, e₀⟩ := halfWeight_comb (fun l => halfWeight_locPot (σ := σ) (L l)) n y
  choose j hj ej using fun l => halfWeight_locPot (σ := σ) (L l) y
  set F : ι → ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun l v => ((L l).φ σ).φ (j l) (c.e.symm v) with hF
  have e : ∀ z, ((ArInt.comb L n).φ σ).φ i₀ z = ∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z := by
    intro z
    have h := e₀ z
    simp only [← ej] at h
    have h2 : ∑ l, (n l : ℝ) * (((L l).φ σ).φ (j l) z / 2) =
        (∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  set Ω := c.e.target ∩ c.e.symm ⁻¹' ⋂ l, ptsIn p σ ((L l).B.U (j l)) with hΩdef
  have hΩ : IsOpen Ω := ChartGlue.isOpen_over c.e (isOpen_iInter_of_finite fun l => isOpen_ptsIn _)
  have hmem : c.e y ∈ Ω := ChartGlue.mem_over c.e hy (Set.mem_iInter.2 hj)
  have hs : ∀ l, ContDiffOn ℝ ∞ (F l) Ω := fun l =>
    (contDiffOn_chart ((L l).cInf σ (j l)) c).mono fun v hv => ⟨hv.1, Set.mem_iInter.1 hv.2 l⟩
  have key : ∀ s : Finset ι,
      ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l ∈ s, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) =
        ∑ l ∈ s, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ (p := fun _ => (0 : ℝ))
        (q := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const 1 hmem
      simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h0
      simp only [Finset.sum_empty]
      exact left_eq_add.1 h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ
        (p := fun w => ∑ l ∈ s, (n l : ℝ) * F l w) (q := F a)
        (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hs l)) (hs a) (n a) hmem
      have h3 : (fun v => ((∑ l ∈ insert a s, (n l : ℝ) * F l v : ℝ) : ℂ)) =
          fun v => ((∑ l ∈ s, (n l : ℝ) * F l v + (n a : ℝ) * F a v : ℝ) : ℂ) := by
        funext v
        rw [Finset.sum_insert ha, add_comm]
      rw [h3, h1, ih, add_comm]
  calc c.hess ((ArInt.comb L n).φ σ) i y = c.hess ((ArInt.comb L n).φ σ) i₀ y :=
        c.hess_eq ((ArInt.comb L n).cInf σ) hy hi₀ hi
    _ = ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) := by
        simp only [AlgChart.hess, e, hF]
    _ = ∑ l, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := key _
    _ = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y :=
        Finset.sum_congr rfl fun l _ => by
          rw [← c.hess_eq ((L l).cInf σ) hy (hm l) (hj l)]
          rfl

end GlobalTheory.Mean4O.ReadsProj
