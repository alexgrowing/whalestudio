import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMonomialProductsLinearIndependentStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem GlobalTheory.ShareOn.lowerRank_oneComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ, (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧ ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  intro E _ _ _ r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  classical
  have hF := GlobalTheory.T.loweredWeight_interpolation_at_points E r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  choose F hFd hFval hFss using hF
  set M := ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X.toData) (Xa.T + 1) with hM'
  have hMcard : M.card = (Xa.T + nd X.toData).choose (nd X.toData) := by
    have e : M = ReciprocityTheory.L2DbarEstimates.Y.multiLe (nd X.toData) Xa.T := by
      ext α
      rw [ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff, ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff]
      omega
    rw [e]
    exact ReciprocityTheory.L2DbarEstimates.Y.ind_count (nd X.toData) Xa.T
  set PM := (Finset.univ : Finset (Fin Fl.δ)) ×ˢ M with hPM
  have hcard : PM.card = Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hMcard]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let f : Fin Fl.δ → (Fin (nd X.toData) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α x => F j x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)
  have hαT : ∀ α ∈ M, ∑ q, α q ≤ Xa.T := fun α hα => by
    rw [hM', ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff] at hα
    omega
  refine ⟨fun q => f (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · exact hFss _ _ (hαT _ (Finset.mem_product.mp (e q).2).2)
  · let cc : (Fin (nd X.toData) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ PM then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ PM := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hlead : ∀ x ∈ X.dom, leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x = 0 := by
      intro x hx
      have h1 : leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x =
          ∑ p ∈ PM, cc p.2 p.1 * f p.1 p.2 x := by
        unfold leadM
        rw [hPM, Finset.sum_product, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
        simp only [f]
        ring
      rw [h1, ← Finset.sum_coe_sort PM, ← e.sum_comp]
      rw [← ha x hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have h7 := GlobalTheory.T.leadingMonomialProducts_linearIndependent E r X.toData Xa Fl F hFd hFval Xa.T cc hlead
    funext q
    rw [← hc q]
    exact h7 _ (Finset.mem_product.mp (e q).2).2 _
