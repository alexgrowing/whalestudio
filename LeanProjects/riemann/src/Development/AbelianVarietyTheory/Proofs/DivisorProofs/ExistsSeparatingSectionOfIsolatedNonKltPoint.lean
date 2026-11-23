import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_sep_of_lcCut : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  intro hNadel X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro M Δ m G N D ρ d x x' hM hΔ hm hG hN hdeg hD hdρ hx hxx' hlc hx'
  haveI hNoeth : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m', D₀, hm', hD₀, rfl, hDn⟩ := hD

  have hq0 : 0 < ρ - d := sub_pos.2 hdρ
  set a : ℕ := (ρ - d).num.toNat with ha_def
  set b : ℕ := (ρ - d).den with hb_def
  have hb : 0 < b := (ρ - d).den_pos
  have hnum : 0 < (ρ - d).num := Rat.num_pos.2 hq0
  have ha : ((a : ℤ) : ℚ) = (ρ - d).num := by
    rw [ha_def, Int.toNat_of_nonneg hnum.le]
  have ha1 : 1 ≤ a := by omega
  have hab : ρ - d = (a : ℚ) / b := by
    have e := Rat.num_div_den (ρ - d)
    rw [← ha, Int.cast_natCast] at e
    exact e.symm
  have hpS : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hNa : IsAmpleLB (lbPow N a) := (isAmpleLB_pow_iff hN.isLB ha1).2 hN
  have hdeg' : ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
      interNumRed ℂ C ![toLB (m' • G + m • D₀)] / ((m * m' : ℕ) : ℚ) +
        interNumRed ℂ C ![lbPow N a] / (b : ℚ) := by
    intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • G + m • D₀))
      (isLB_lbPow (isLB_toLB G) m') (isLB_lbPow (isLB_toLB D₀) m)
      (by rw [cls_lbPow (isLB_toLB G), cls_lbPow (isLB_toLB D₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB G), hC.interNumRed_lbPow hH (isLB_toLB D₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have h3 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hD' := hDn C hC
    rw [div_eq_iff h2] at hD'
    rw [hdeg C hC, e, hC.interNumRed_lbPow hH hN.isLB a, show ρ = d + a / b by linarith]
    push_cast
    rw [hD']
    field_simp
    ring
  obtain ⟨J, hJ, hvan⟩ := hNadel X p n hp hn M (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) b
    (lbPow N a) hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', D₀, hm', hD₀, rfl⟩)
    (Nat.mul_pos hm hm') (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG) hb
    hNa.isNef (IsAmpleLB.isBig ℂ X hpS _ hNa) hdeg'
  have hxJ : x ∈ J.support := (hJ x).2 hlc.2.1
  have hx'J : x' ∈ J.support := (hJ x').2 hx'
  obtain ⟨U, hxU, hU⟩ := exists_open_inter_eq_singleton_of_no_generisation X (J.support : Set X) x
    J.support.isClosed hx hxJ fun z hz hzx => by
      by_contra hne
      obtain ⟨e, -, he, h1⟩ := closure_point_topologicalKrullDim X n z hn
      have h0 := hlc.2.2 z hzx ((hJ z).1 hz)
      have he1 := h1 x hzx (Ne.symm hne)
      rw [he] at h0
      have : e ≤ 0 := by exact_mod_cast h0
      omega
  obtain ⟨s, hs1, hs2⟩ := exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ X p hp M hM J x U hx
    hxU hU (hvan 1 one_pos)
  exact ⟨s, hs1, hs2 x' hx'J (Ne.symm hxx')⟩

end GlobalTheory.PairStep
