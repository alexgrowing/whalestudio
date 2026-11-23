import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosNatMemFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceFormIntegralPerfectOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CovData

theorem hasPrinc_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
      (Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd)) := by
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hN : 3 ≤ D.host.g 0 * D.host.g 1 * Y.d.pd := by
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 4 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
    nlinarith
  intro k γ hγ hc
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((D.host.g 0 * D.host.g 1 * Y.d.pd : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul])
  obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩
  have h1 := GlobalTheory.PrincCore.root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD
    hmu _ hN hG.levelK k γ γ' hγ'
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((Y.d.l₂.M : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul, mul_comm])
    u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.CovData

namespace GlobalTheory.CovData

theorem exists_dataX_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T j Y e o hG σ hσ k
  obtain ⟨hr, hm⟩ := hG.modelW σ hσ
  have hx1 : xiR D ≤ 1 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_le_half D).trans (by norm_num)
  have habs := hG.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) k
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((Y.U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [(hm k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
      ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
    exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e0
    rw [e0] at hone
    simp at hone
  have hM : 0 < Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    have hp : 0 < Y.d.pd := by rw [hG.pd]; positivity
    have hl : 0 < Y.d.l₂.M := by have := Y.d.l₂.three_le; omega
    positivity
  obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((Y.U σ).X k) D.host.AA D.host.AAbar
    (xiR D) _
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hasPrinc_good D T j Y e o hG σ hσ k)
  exact ⟨Xx, D.host.AA, h1, hA, h3⟩

end GlobalTheory.CovData
