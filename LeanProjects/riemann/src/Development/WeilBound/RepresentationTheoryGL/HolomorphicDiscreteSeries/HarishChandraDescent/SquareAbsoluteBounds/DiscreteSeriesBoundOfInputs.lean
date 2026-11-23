import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace NormTraceLemmas

theorem abs_le_of_nsq {n : ℕ} (u : Fin n → ℝ) (T : ℝ) (h : nsq u ≤ T) (a : Fin n) : |u a| ≤ Real.sqrt T := by
  have hs : u a ^ 2 ≤ nsq u := by
    unfold nsq dot
    have := Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ a)
    simpa [sq] using this
  exact Real.abs_le_sqrt (hs.trans h)

end NormTraceLemmas

theorem discrete_series_bound_of_inputs : Comp → Parts → Cut → Ascent → Descent → IntWt → HCOf → Ident → Core := by
  intro hComp hParts hCut hAsc hDesc hInt hHCOf hId
  unfold Comp ForAlg at hComp
  unfold Parts ForAlg at hParts
  unfold Cut ForRep at hCut
  unfold Ascent ForAlg at hAsc
  unfold Descent ForAlg at hDesc
  unfold IntWt ForRep at hInt
  unfold HCOf at hHCOf
  unfold Ident ForRep at hId
  unfold Core ForRep
  intro n ε H _ _ _ ρ hU hD μ S τ J x hS hx hK hq hgap hJ hτ
  have hDer := isDerivedOn_smE hU
  have hGl := hDer.glRep
  have hIU := isInfUnitary_of_isDerivedOn hU hDer
  obtain ⟨y, ν, κ, hG, hqy⟩ := hComp n ε _ (smE ε ρ) hGl hIU μ S x hx hK hq
  obtain ⟨h1, h2, h3⟩ := hParts n ε _ (smE ε ρ) hGl hIU μ ν κ S y hG hqy
  obtain ⟨N, hN, hNcas, y', hy'N, hG'⟩ := hCut n ε H ρ hU hD ν κ S y hS hG h3
  have hsq : 0 ≤ √(2 * S) := Real.sqrt_nonneg _
  have hn3 : (0:ℝ) ≤ (n:ℝ) ^ 3 := by positivity
  have hJ0 : (0:ℝ) ≤ (J:ℝ) := by positivity
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hτ0 : 0 ≤ τ := by linarith
  have hanti : Antitone μ := by
    intro a b hab
    rcases hab.lt_or_eq with h | h
    · have := hgap a b h
      linarith
    · rw [h]
  obtain ⟨y'', hy''N, L, hy0, hyK, hHW, hcasL, hLμ⟩ :=
    hAsc n ε _ (smE ε ρ) hGl hIU N hN μ ν κ S y' hy'N hG' hanti h1 h2
  have hbd : ∀ a, |L a - μ a| ≤ √(2 * S) := fun a => by
    have := NormTraceLemmas.abs_le_of_nsq (L - μ) (2 * S) hLμ a
    simpa using this
  obtain ⟨L', V, hL'bd, hIrr, hNoD⟩ :=
    hDesc n ε _ (smE ε ρ) hGl hIU N hN μ L (2 * S) τ (√(2 * S)) J
      (fun z hz => by rw [hcasL]; exact hNcas z hz) hgap hbd hJ y'' hy''N hy0 hyK hHW
  obtain ⟨w, -, hw0, hwHW⟩ := hIrr.2.2.2
  have hLint := hInt n ε H ρ hU L' w hw0 hwHW.1
  have hgapL : ∀ a b : Fin n, a < b →
      (τ - 2 * (√(2 * S) + J) - 2 * n) + 2 * n ≤ L' a - L' b := by
    intro a b hab
    have ha := abs_le.mp (hL'bd a)
    have hb := abs_le.mp (hL'bd b)
    have := hgap a b hab
    linarith [ha.1, ha.2, hb.1, hb.2]
  have hh : 0 < τ - 2 * (√(2 * S) + J) - 2 * n := by linarith
  obtain ⟨mu, hP, hlow, hGap, hmu⟩ := hHCOf n ε L' _ hLint hh hgapL
  have hlt : (n:ℝ) ^ 3 + 2 * n + 1 < τ - 2 * (√(2 * S) + J) - 2 * n := by linarith
  have hV1 : IsKIrrHW ε (smE ε ρ) (lowK ε mu) V := by rw [hlow]; exact hIrr
  have hV2 : NoDown ε (smE ε ρ) (lowK ε mu) V := by rw [hlow]; exact hNoD
  refine ⟨mu, hP, fun a => ?_, ?_⟩
  · have e1 := hmu a
    have e2 := hL'bd a
    have e3 := abs_sub_le (mu a) (L' a) (μ a)
    linarith
  · intro H' _ _ _ σ hσ
    exact hId n ε H ρ hU mu _ hP hGap hlt V hV1 hV2 H' σ hσ

end PositivityTheory.RgHe3
