import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAtBoundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdStalkExt

theorem exists_extension_test {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ N : LB (pullback g (S.fromSpecStalk x)), N.IsLB ∧
      ∀ (T : Scheme.{0}) (a : T ⟶ pullback g (S.fromSpecStalk x)) (b : T ⟶ Y),
        a ≫ pullback.fst g (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.BdLocalExt.exists_extension_stalk g e x L hL
  refine ⟨N, hN, fun T a b hab => ?_⟩
  let t : T ⟶ pullback (e ≫ g) (S.fromSpecStalk x) :=
    pullback.lift b (a ≫ pullback.snd g (S.fromSpecStalk x)) (by
      rw [← Category.assoc, ← hab, Category.assoc, Category.assoc, pullback.condition])
  have ha : a = t ≫ pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [hab, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hb : b = t ≫ pullback.fst (e ≫ g) (S.fromSpecStalk x) := (pullback.lift_fst _ _ _).symm
  exact LBIso.chartPull (chartPullSame N _ _ _ t fun _ => ha) (chartPullSame L _ _ _ t fun _ => hb) h

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_test G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdStalkExt
