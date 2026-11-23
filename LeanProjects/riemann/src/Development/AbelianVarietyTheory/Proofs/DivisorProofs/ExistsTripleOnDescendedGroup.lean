import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtendedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricCubicalBundleExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidCubicalExtensionPullbackOfToricChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescTriple

theorem exists_triple_of_group_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ t : SAB H S, abLocus t.G = abLocus G ∧ Nonempty (SABMap tF t j) ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t t ξ) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hns Z zs i OZ N d J S π j _ BD hU _hSep hPre tF mF G _ _ e hsemi he hch
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_ringAction_extend_descended_semiAbelian Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch
  obtain ⟨PP, cub, sym, cm, hcm, hce, hlin⟩ :=
    GlobalTheory.T.exists_rigidified_symmetric_cubicalBundle_extension Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch
  have adj := GlobalTheory.T.hermitianAdjointnessIso_extends_descendedGroup Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch act hact PP cub cm
    hcm hce hlin
  have prim := GlobalTheory.T.principalPolarisationIso_extends_descendedGroup Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch act hact PP cub cm
    hcm hce hlin
  let t : SAB H S := ⟨G, hsemi, act, PP, cub, sym, adj, prim⟩
  refine ⟨t, rfl, ⟨⟨cm, hcm ▸ he, hce, fun a => by rw [hcm]; exact hact a, hlin⟩⟩, ?_⟩
  intro k _ m n C hC ξ hξ
  obtain ⟨tK, ⟨a⟩, ⟨mU⟩⟩ := C.gen
  obtain ⟨b, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t tF tK (pullback.fst _ _) C.y mF mU
  obtain ⟨πC, hπ, hab⟩ := hch C hC ξ hξ tK a b
  have hactC := GlobalTheory.T.chart_ringAction_compatible_extended C.t G ξ πC hsemi hπ act tK a (b.φ ≫ e) (fun u => by
    rw [← Category.assoc, b.act u, Category.assoc, hact u, Category.assoc]) hab
  obtain ⟨cm', hcm', hce', hlin'⟩ :=
    GlobalTheory.T.rigidCubicalExtension_pullback_of_toricChart C.t G ξ πC hsemi hπ PP cub tF j e cm hcm hce hlin C.y hξ tK a b hab
  exact ⟨⟨cm', hcm' ▸ hπ, hce', fun u => by rw [hcm']; exact hactC u, hlin'⟩⟩

end GlobalTheory.DescTriple
