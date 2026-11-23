import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomainStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartDesc

theorem exists_semiAbelian_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP hpre tF mF
  have hNoeth : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP.2.2.2.2.1.2.1
  have hNorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).1 hP.2.2.2.2.1.1.1
  have hdom : IsDominant j := ⟨hP.2.2.2.2.1.2.2.2.1⟩
  have hAab : IsAbelianScheme tF.G :=
    ⟨tF.comm, tF.semi.smooth, MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper, tF.semi.geomConnected⟩
  have hLB : tF.PP.L.IsLB := tF.PP.isLB
  have hAmp : RelAmple tF.G tF.PP.L := GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple Xo c tF mF
  have hkc : ∀ (k : Type) [Field k], IsAdicComplete (maximalIdeal k) k := fun k _ => by
    rw [maximalIdeal_eq_bot]; infer_instance

  have bdChart : ∀ (x : S) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e))
      (ξ : Sp (ChartRing k m e) ⟶ S), C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) = x →
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ∃ Ch : GlobalTheory.Desc.Chart j tF.G x, ∀ (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ π : Ch.G.left ⟶ G.left,
        IsGrpPullback Ch.G G Ch.ξ π → (x ∈ abLocus G ↔ closedPoint (ChartRing k m e) ∈ abLocus C.t.G) := by
    intro x k _ m e C ξ hy hcl het
    haveI : CharZero (ChartRing k m e) := charZero_of_injective_ringHom C.b.injective
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    haveI := hkc k
    obtain ⟨α, hα⟩ := GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple Xo c (ChartRing k m e) C.y C.t tF C.gen mF
    refine ⟨{ R := ChartRing k m e
              complete := GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
              charZero := inferInstance
              ξ := ξ
              centre := hcl
              etc := het
              unr := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ het
              G := C.t.G
              semi := C.t.semi
              y := C.y
              hy := hy
              α := α
              gen := hα }, ?_⟩
    intro G _ hG π hπ
    rw [← hcl]
    exact abLocus_pullback abLocusOne hG hπ.1 (closedPoint _)
  have hch : ∀ x : S, Nonempty (GlobalTheory.Desc.Chart j tF.G x) := by
    intro x
    by_cases hx : x ∈ Set.range j
    · exact GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart Xo c j tF.G tF.semi x hx
    · obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, -⟩ := hpre x hx
      obtain ⟨Ch, -⟩ := bdChart x k m e C ξ hy hcl het
      exact ⟨Ch⟩
  obtain ⟨G, _, e, hG, hpb, hmap⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts (Xo.XF c) S hNorm j hdom tF.G hAab tF.PP.L hLB hAmp hch
  haveI : IsCommMonObj G := hG.comm
  refine ⟨G, inferInstance, hG.comm, e, hG, hpb, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_contra hxj
      obtain ⟨k, _, m, e', C, ξ, a, htaut, hy, hcl, het, -, hset, -⟩ := hpre x hxj
      obtain ⟨Ch, hCh⟩ := bdChart x k m e' C ξ hy hcl het
      obtain ⟨π', hπ', -⟩ := hmap x Ch
      have hcp := (hCh G hG π' hπ').1 hx
      have hprod : ∏ i, C.s i ∈ (closedPoint (ChartRing k m e')).asIdeal := by
        by_contra hn
        exact hxj (hcl ▸ (hset _).2 hn)
      have hm : 1 ≤ C.m := by
        rcases Nat.eq_zero_or_pos C.m with h0 | h0
        · exfalso
          haveI : IsEmpty (Fin C.m) := by rw [h0]; infer_instance
          rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
          exact (maximalIdeal (ChartRing k m e')).ne_top_iff_one.1 (maximalIdeal.isMaximal _).ne_top hprod
        · exact h0
      exact GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart Xo c φ k m e' C htaut hm hcp
    · rintro ⟨x', rfl⟩
      rw [abLocus_pullback abLocusOne hG hpb.1 x']
      intro K _ _ t _
      haveI := hAab.proper
      infer_instance
  · intro k _ m n C hC ξ hξ tK a b
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
    haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).2
    exact GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain (ChartRing k m n) j tF.G G e hG hpb C.t.G C.t.semi ξ C.y hξ tK.G a.φ b.φ a.cart b.cart

theorem exists_semiAbelian_of_charts_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP _ hpre tF mF
  exact exists_semiAbelian_of_charts Xo c φ hpq hfan hnsi zs i OZ N d J π j BD hP hpre tF mF

end GlobalTheory.UChartDesc
