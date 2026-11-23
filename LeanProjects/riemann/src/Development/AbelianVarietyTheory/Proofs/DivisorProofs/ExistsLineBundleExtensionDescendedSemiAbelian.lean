import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedLineBundleExtensionOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescLBExt

theorem exists_lb_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ M : LB G.left, M.IsLB ∧ LBIso (M.pull e) tF.PP.L := by
  intro E _ _ _ H Dw l Xo c φ h1 h2 h3 Z zs i OZ N d J S π j _ BD hU hpre tF hmap G _ _ e hsa he hch
  have hU' := hU
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU'
  have := hsa.smooth
  have := hsa.geomConnected
  have := hsa.quasiCompact
  have := hsa.separated
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  haveI := GlobalTheory.IsNormalScheme.of_pred hS
  have hst := GlobalTheory.T.exists_lineBundle_extension_at_boundaryPoint Xo c φ h1 h2 h3 zs i OZ N d J π j BD hU hpre tF hmap G e hsa he hch
  exact GlobalTheory.T.exists_rigidifiedLineBundle_extension_of_local G.hom j hdense e tF.G.hom he.1 (eSec G) (eSec tF.G) (Over.w η[G]) (cubeMapOf he).e_comm
    tF.PP.L tF.PP.isLB tF.PP.rig tF.PP.rigGen fun x hx => by
      obtain ⟨Nx, hNx, hx'⟩ := hst x hx
      exact GlobalTheory.T.exists_lineBundle_spread_from_localScheme G.hom j e tF.G.hom he.1 tF.PP.L tF.PP.isLB x Nx hNx hx'

end GlobalTheory.DescLBExt
