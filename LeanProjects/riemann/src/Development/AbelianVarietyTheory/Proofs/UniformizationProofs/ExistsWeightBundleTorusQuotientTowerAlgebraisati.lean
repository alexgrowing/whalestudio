import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

theorem exists_levels (t : Tower s) (χ : s.X) : ∃ (N : ∀ e, LB (t.l e).Q.B.left)
    (u : ∀ e, LB.Gen ((N e).pull (t.l e).Q.q.left)),
    ∀ e, (N e).IsLB ∧ (t.l e).Q.GenWt (N e) (u e) χ ∧ Triv (abelian₂ (t.l e).Q.B (N e)) := by
  have H : ∀ e, ∃ (N : LB (t.l e).Q.B.left) (u : LB.Gen (N.pull (t.l e).Q.q.left)),
      N.IsLB ∧ (t.l e).Q.GenWt N u χ ∧ Triv (abelian₂ (t.l e).Q.B N) := by
    intro e
    haveI := isLocalRing_quotient_pow V e
    obtain ⟨N, u, hN, hu, g, hg⟩ := GlobalTheory.exists_weight_bundle _ _ _ (t.l e).Q χ
    exact ⟨N, u, hN, hu, g, hg⟩
  choose N u h using H
  exact ⟨N, u, h⟩

theorem lbIso_succ (t : Tower s) {χ : s.X} (e : ℕ) {N : LB (t.l e).Q.B.left} {N' : LB (t.l (e + 1)).Q.B.left}
    {u : LB.Gen (N.pull (t.l e).Q.q.left)} {u' : LB.Gen (N'.pull (t.l (e + 1)).Q.q.left)} (hN : N.IsLB)
    (hN' : N'.IsLB) (hu : (t.l e).Q.GenWt N u χ) (hu' : (t.l (e + 1)).Q.GenWt N' u' χ) :
    LBIso N (N'.pull (t.β e)) := by
  obtain ⟨v, hv⟩ := exists_genWt_pull (t.l (e + 1)).Q (t.l e).Q
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) G e) (t.tor e) (t.β_q e) hu'
  exact lbIso_of_genWt _ _ _ (t.l e).Q N (N'.pull (t.β e)) u v χ hN (pull_isLB hN' _) hu hv

theorem isPullback_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    (h : IsCPPullback M' M f β) : IsPullback β B'.hom B.hom f := by
  obtain ⟨hg, -⟩ := h
  exact hg.1

theorem exists_alg_of_lbIso {V : Type} [CommRing V] [IsDomain V] [i : IsLocalRing V] (hV : CDVR V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e))
    (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) (hp : IsProjBy B.hom) (hf : Flat B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hc : ∀ e, β e ≫ b (e + 1) = b e) (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) :
    ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  choose w hw using h
  exact GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hp hf hb hc N w fun e => ⟨hN e, hw e⟩

theorem isPullback_β (t : Tower s) (e : ℕ) : IsPullback (t.β e) (t.l e).Q.B.hom (t.l (e + 1)).Q.B.hom
    (thickTrans V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (t.β_pb e)

theorem isPullback_b {t : Tower s} (a : t.Alg) (e : ℕ) : IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom
    (thick V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (a.b_pb e)

theorem flat_alg {t : Tower s} (a : t.Alg) : Flat a.B.hom := by
  haveI := a.isAb.smooth
  infer_instance

theorem exists_alg {t : Tower s} (a : t.Alg) (N : ∀ e, LB (t.l e).Q.B.left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e))) :
    ∃ O : LB a.B.left, O.IsLB ∧ ∀ e, LBIso (N e) (O.pull (a.b e)) := by
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  exact exists_alg_of_lbIso s.cdvr (fun e => (t.l e).Q.B) t.β (isPullback_β t) a.B a.b hp (flat_alg a)
    (isPullback_b a) a.b_β N hN h

theorem triv_lam_alg (hG : GlobalFnsSt) {t : Tower s} (a : t.Alg) {N : ∀ e, LB (t.l e).Q.B.left}
    (hN : ∀ e, (N e).IsLB) {O : LB a.B.left} (hO : O.IsLB) (hi : ∀ e, LBIso (N e) (O.pull (a.b e)))
    (h : ∀ e, Triv (abelian₂ (t.l e).Q.B (N e))) : Triv (abelian₂ a.B O) := by
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  refine triv_lam_of_levels hG a.isAb hp hO fun e => ?_
  obtain ⟨hb, -⟩ := a.b_pb e
  exact triv_lam_pull hb hO (hN e) (hi e) (h e) (fstG (IsLocalRing.maximalIdeal V) e (a.B ⊗ a.B))

theorem exists_weight_bundle_alg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  intro hL V _ _ _ A G _ _ s t a χ
  obtain ⟨N, u, h⟩ := exists_levels t χ
  have hiso : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e)) := fun e =>
    lbIso_succ t e (h e).1 (h (e + 1)).1 (h e).2.1 (h (e + 1)).2.1
  obtain ⟨O, hO, hi⟩ := exists_alg a N (fun e => (h e).1) hiso
  have hT := triv_lam_alg hL.globalFns a (fun e => (h e).1) hO hi (fun e => (h e).2.2)
  refine ⟨O, hO, hT, fun e => ?_⟩
  obtain ⟨v, hv⟩ := exists_genWt_of_lbIso (t.l e).Q (h e).1 (pull_isLB hO _) (hi e) (h e).2.1
  exact exists_gen_comp (t.l e).Q (a.b e) hv

end GlobalTheory.WtTower
