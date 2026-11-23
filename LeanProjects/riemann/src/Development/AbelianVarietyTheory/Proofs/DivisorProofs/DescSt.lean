import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

theorem descSt : GlobalTheory.SiegJoin.DescSt := by
  intro g _ φ n hn _ F Z z i OZ d S π j _ BD _ hB _ hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.descended_group_abelianLocus_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
