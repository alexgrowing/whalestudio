import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SabBaseChangeStIffFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrimExt

theorem refl_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_of_range_subset {X Y Y' : Scheme.{0}} (e : Y ⟶ X) [IsOpenImmersion e] (f : Y' ⟶ X)
    (hf : Set.range f.base ⊆ Set.range e.base) (L M : LB X) (h : LBIso (L.pull e) (M.pull e)) :
    LBIso (L.pull f) (M.pull f) := by
  have hc : f = IsOpenImmersion.lift e f hf ≫ e := (IsOpenImmersion.lift_fac e f hf).symm
  exact LBIso.chartPull (chartPullSame L _ _ _ _ fun _ => hc) (chartPullSame M _ _ _ _ fun _ => hc) h

theorem prim_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (tF : SAB H S') (G : Over S) [GrpObj G] [IsCommMonObj G] (j : S' ⟶ S) (e : tF.G.left ⟶ G.left)
    (he : IsGrpPullback tF.G G j e) (act : OAct (𝓞 E) G)
    (hact : ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) (PP : RigLB G)
    (hw : LBIso tF.PP.L (PP.L.pull e)) :
    LBIso (PP.L.pull e) ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) := by
  have hP : (PP.L.pull e).IsLB := pull_isLB PP.isLB e
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  let U := pushPt he.1.w (𝟙 tF.G)
  have hU : U.left = e := by simp [U, pushPt]
  have hc : ∀ I : ULift.{0} (Finset (Fin 2)),
      (psum tF.G ![𝟙 tF.G, tF.act.act H.w0] I.down).left ≫ e = e ≫ (psum G ![𝟙 G, act.act H.w0] I.down).left :=
    fun I => (psum_push he ![𝟙 tF.G, tF.act.act H.w0] ![𝟙 G, act.act H.w0] U (fun i => by
      fin_cases i
      · apply Over.OverMorphism.ext
        simp [U, pushPt]
      · apply Over.OverMorphism.ext
        simp [U, pushPt, hact]) I.down).trans (by rw [hU])
  have h4 : LBIso (cubeLB tF.G ![𝟙 tF.G, tF.act.act H.w0] (PP.L.pull e))
      ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) :=
    LBIso.chartPull (chartPullLinComb PP.L e _ _ _ e hc) (chartPullPull _ e) (refl_of_isLB hC)
  refine LBIso.trans hP tF.PP.isLB (pull_isLB hC e) hw.symm ?_
  refine LBIso.trans tF.PP.isLB (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (pull_isLB hC e) tF.prim ?_
  exact LBIso.trans (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (GlobalTheory.SabPullCompare.cubeLB_isLB _ hP)
    (pull_isLB hC e) (GlobalTheory.SabPullCompare.lbIso_cubeLB _ hw) h4

theorem lbIso_prim_ext : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hUP _ tF _ G _ _ e hG he _ act hact PP cub cm hF _ hlin
  obtain ⟨-, -, -, -, ⟨⟨hS, -⟩, hproj, -, hdense, -⟩, -⟩ := hUP
  have : IsLocallyNoetherian S := by
    obtain ⟨N', im, _, h⟩ := hproj
    have : LocallyOfFiniteType (π ≫ zs) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := by haveI := hS; exact GlobalTheory.IsNormalScheme.pred S
  have hw : LBIso tF.PP.L (PP.L.pull e) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact hF ▸ ⟨w, hw⟩
  have : IsOpenImmersion e := MorphismProperty.of_isPullback he.1.flip inferInstance
  have hr : Set.range e.base = G.hom.base ⁻¹' Set.range j.base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show (e ≫ G.hom) y ∈ Set.range j
      rw [he.1.w]
      exact ⟨_, rfl⟩
    · intro hx
      have hx' : x ∈ Set.range (pullback.fst G.hom j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      obtain ⟨z, rfl⟩ := hx'
      refine ⟨he.1.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he.1.isoPullback_inv_fst]
  haveI := act.hom H.w0
  haveI := hG.smooth
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  let V : S.Opens := j.opensRange
  haveI : IsDominant V.ι := ⟨by
    show Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    simpa [V] using hdense⟩
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  have hsec : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  have hrig : CechPic.pull (eSec G) (CechPic.cls PP.L PP.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  refine (CechPic.cls_eq_iff PP.isLB hC).1 (GlobalTheory.ZH.EndoExtend.pic_ext V.ι hS' G (eSec G) hsec ?_ ?_)
  · rw [hrig, GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ PP.isLB]
    have hp := GlobalTheory.ZH.EndoExtend.pull_cubeCls G ![𝟙 G, act.act H.w0]
      (fun _ : Fin 2 => (η[G] : 𝟙_ (Over S) ⟶ G)) η[G]
      (fun i => by
        fin_cases i
        · simp
        · simp [IsMonHom.one_hom]) (CechPic.cls PP.L PP.isLB)
    exact (GlobalTheory.ZH.EndoExtend.cubeCls_one G _ hrig).symm.trans hp.symm
  · refine (CechPic.cls_eq_iff (pull_isLB PP.isLB _) (pull_isLB hC _)).2 ?_
    refine lbIso_pull_of_range_subset e _ ?_ _ _ (prim_pull tF G j e he act hact PP hw)
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    rfl

end GlobalTheory.PrimExt
