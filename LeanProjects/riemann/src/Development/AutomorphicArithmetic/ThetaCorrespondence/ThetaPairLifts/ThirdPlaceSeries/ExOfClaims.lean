import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDataExistenceOfSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.LeafRestExamples
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000 in
theorem ex_of_claims_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK → GlobalTheory.RowClaim.ConstK → (_root_.GlobalTheory.BigTop.Fun.CharacterAtPoint fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) → GlobalTheory.NormSum.IntSt → FieldDat → TorEx → DenEx → BotEx → BotSmall → _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn @Fld @Comparison₂ := by
  intro hSet hdl hS hR hC hr hI hFD hT hD hB hBS
  obtain ⟨c1, h1⟩ := hSet.atPt hS
  obtain ⟨c2, h2⟩ := hSet.atPt hR
  obtain ⟨c3, h3⟩ := hSet.atPt hC
  obtain ⟨c4, h4⟩ := hr
  obtain ⟨c5, h5⟩ := Model.gBig_and (Model.gBig_and hT hD) (Model.gBig_and (Model.gBig_and hB hBS) hFD)
  obtain ⟨CI, -, hI⟩ := exists_isIntExp hI
  refine ⟨max (max (max c1 c2) (max c3 c4)) (max c5 CI), fun CF hCF => ?_⟩
  have k1 : c1 ≤ CF := le_trans (by simp) hCF
  have k2 : c2 ≤ CF := le_trans (by simp) hCF
  have k3 : c3 ≤ CF := le_trans (by simp) hCF
  have k4 : c4 ≤ CF := le_trans (by simp) hCF
  have k5 : c5 ≤ CF := le_trans (by simp) hCF
  have k6 : CI ≤ CF := le_trans (by simp) hCF
  obtain ⟨e0, he0, H⟩ := (((h1 CF k1).and (h2 CF k2)).and ((h3 CF k3).and (h4 CF k4))).and (hdl.and hSet)
  refine ⟨e0, he0, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  obtain ⟨C0, x₀, hg⟩ := h5 eps CF k5
  refine ⟨K, fun Fm CH hc hL _ => ?_⟩
  obtain ⟨⟨⟨⟨y1, g1⟩, ⟨y2, g2⟩⟩, ⟨⟨y3, g3⟩, ⟨y4, g4⟩⟩⟩, ⟨y5, g5⟩, ⟨y6, g6⟩⟩ := hK Fm CH hc hL
  refine ⟨max (max (max y1 y2) (max y3 y4)) (max (max y5 y6) x₀), fun x hx hle i p hp G W hW _ hF => ?_⟩
  have l1 : y1 ≤ x := le_trans (by simp) hle
  have l2 : y2 ≤ x := le_trans (by simp) hle
  have l3 : y3 ≤ x := le_trans (by simp) hle
  have l4 : y4 ≤ x := le_trans (by simp) hle
  have l5 : y5 ≤ x := le_trans (by simp) hle
  have l6 : y6 ≤ x := le_trans (by simp) hle
  have l7 : x₀ ≤ x := le_trans (by simp) hle
  obtain ⟨n, a, ha⟩ := hF
  have hset := g6 x hx l6 i p hp ha.eser
  have hrec : Rec (Fm.L x i) := ⟨hset.size, hset.host, hset.hF, g5 x hx l5 i p hp⟩
  obtain ⟨⟨hTor, hDen⟩, ⟨hBot, hSm⟩, hFd⟩ := hg C0 le_rfl _ (Fm.L x i) (Fm.L_eps x i)
    (by rw [Fm.L_x x i hx]; exact l7) hrec _ _ _ hset.core.lev G
  have hb : Real.log (Fm.L x i).sc.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL1 : 1 ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hlog1 : 1 ≤ Real.log (Fm.L x i).sc.b := hb ▸ hL1
  have hrd : Real.log (Fm.D x i).host.rdE ≤ Real.log (Fm.L x i).sc.b := by
    have e1 := hset.size.2.2.2.2.2.2.2.2.2.1
    have e2 := hset.size.2.2.2.2.2.2.2.2.2.2.1
    rw [hb]; linarith
  obtain ⟨dl, hdl⟩ := hI _ _ _ _ G hSm.1 hlog1 hrd
  obtain ⟨δ, t0, hBot'⟩ := hBot
  obtain ⟨_, _, _, _, Λ, hΛ⟩ := hFd
  refine TieModel.exists_tie hW a ha (g1 x hx l1 i p hp G W n a ha) (g2 x hx l2 i p hp G W n a ha ha.field)
    (g3 x hx l3 i p hp G W n a ha) (g4 x hx l4 i p hp G W n a ha)
    ⟨δ, t0, fun ij => let ⟨P, P', h⟩ := hBot' ij; ⟨P, P', h, trivial, trivial⟩⟩ (fun ij s hs1 hs2 => ?_)
    ⟨dl, TieModel.isIntExp_mono (zero_le_one.trans hlog1) hdl k6⟩
  obtain ⟨nn, hnn, hfin⟩ := hDen ij.1 ij.2 s hs1 hs2
  obtain ⟨x0', hx0, hx0ne, -, halg⟩ := hTor ij.1 ij.2 s hs1 hs2 none
  have hz : ∀ c : Bool, ∃ z, IsTor G ij.1 ij.2 s (nuH G p.P.A3.A.μ0 ij.1 ij.2 * delOf _ c)
      ((Fm.D x i).what₂.embLL z * x0') := fun c => by
    obtain ⟨y, hy, -⟩ := hTor ij.1 ij.2 s hs1 hs2 (some c)
    obtain ⟨z, hz⟩ := ha.sq.toric ij.1 ij.2 s c x0' y hs1 hs2 hx0 hy
    exact ⟨z, by rw [hz, div_mul_cancel₀ _ hx0ne]; exact hy⟩
  choose zd hzd using hz
  obtain ⟨pp, hpp⟩ := exists_isMinPol (σ := (Fm.D x i).what₂.embLL) (halg Λ hΛ)
  exact ⟨zd, fun w => truncZero (meanVal_vw w pp / 12), nn, ⟨x0', hx0, hx0ne, hzd, Λ, pp, hΛ, hpp, fun w => rfl⟩, hnn, hfin⟩
end GlobalTheory.BigTop.Fun
end
end
