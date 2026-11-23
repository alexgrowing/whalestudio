import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverDegreeOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

namespace GlobalTheory.PPAS

theorem HasTheta.of_isPull {S S' : Scheme.{0}} {P : PPAS S} {P' : PPAS S'} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (hP : P'.IsPull P f φ) (hT : P.HasTheta) : P'.HasTheta := by
  obtain ⟨h, hc⟩ := hP
  obtain ⟨L, hL, hs, e⟩ := hT
  have hL' := pull_isLB hL φ
  refine ⟨L.pull φ, hL', PolBaseChange.sym_pull h hs, ?_⟩
  rw [hc, e, pull_sqMap_lam h, CechPic.cls_pull hL φ hL']

theorem exists_pull_regCover_ch2Omega : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration →
    ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p →
    ∀ (C : RegCover p) (P : PPAS S), P.HasTheta → ∃ P' : PPAS C.Y, P'.g = P.g ∧ P'.HasTheta ∧
      P'.degOmega (C.ρ ≫ p) = C.deg * P.degOmega p ∧
      ∀ a : ℝ, P.IsCh2Omega p a → P'.IsCh2Omega (C.ρ ≫ p) (C.deg * a) := by
  intro HP HR k _ S p _ hS C P hT
  obtain ⟨P', φ, hg, hP⟩ := exists_pull S C.Y P C.ρ
  obtain ⟨hd, hc⟩ := CoverHodge.degOmega_ch2Omega_cover HP HR k S p hS.toIsArithVar P C P' φ hP
  refine ⟨P', hg, hT.of_isPull hP, hd, fun a ha => ?_⟩
  obtain ⟨h', H', -, hc', -⟩ := exists_isHodge_ch2Omega HP.p4 k C.Y (C.ρ ≫ p)
    (fun Y q _ hq => RegCoverExists.nonempty_regCover HR k Y q hq) C.reg.toIsArithVar P'
  have hb : P'.IsCh2Omega (C.ρ ≫ p) (P'.ch2Omega (C.ρ ≫ p)) := ⟨h', H', hc'⟩
  have e := (hc _ hb).unique ha
  have hn : (C.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 C.deg_pos.ne'
  convert hb using 1
  rw [← e]
  field_simp

end GlobalTheory.PPAS
