import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Cf

def PF {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (T : TorusExtension G) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso L (M.pull T.q.left)

def teBC {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    isAbelian :=
      { comm := by have := T.isAbelian.comm; infer_instance
        smooth := by have := T.isAbelian.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := T.isAbelian.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := T.isAbelian.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    q := Out.GtBCPf.qB f T.q
    q_hom := inferInstance
    q_flat := Out.GtBCPf.qB_flat f T.q T.q_flat
    q_surjective := Out.GtBCPf.qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (Out.GtBCPf.qB_sq f T.q) T.q_quasiCompact
    i := Out.GtBCPf.iB f T.X T.i
    i_hom := Out.GtBCPf.iB_hom f T.X T.i
    isKernel := Out.GtBCPf.iB_isKernel f T.X T.q T.i T.isKernel }

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show _ * _ * gm (𝟙 X) y (L.U q.1 ⊓ L.U q.2) (L.g q.1 q.2) = gm (𝟙 X) y (L.U p.1 ⊓ L.U p.2) (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X)
    (e : g ≫ F = h) : LBIso (L.pull h) ((L.pull F).pull g) :=
  LBIso.chartPull (chartPullId _) (chartPullLinComb L F (fun _ : PUnit => g) (fun _ => h) (fun _ => 1) (𝟙 Z)
    fun _ => e.trans (Category.id_comp _).symm) (lbIso_refl (pull_isLB hL h))

theorem pf_pull {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    {G₂ : Over (Sp k₂)} [GrpObj G₂] {φ : G₂.left ⟶ G.left} (h : IsGrpPullback G₂ G f φ) {L : LB G.left}
    {L₂ : LB G₂.left} (hL : L.IsLB) (hL₂ : L₂.IsLB) (w : LBIso L₂ (L.pull φ)) (H : PF G L) : PF G₂ L₂ := by
  obtain ⟨T, M, hM, hK, hi⟩ := H
  let := T.grpB
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h
  have hM₂ := pull_isLB hM (pullback.fst T.B.hom f)
  obtain ⟨u, hu⟩ := lbIso_refl hM₂
  have hK₂ := kTriv_pull (isGrpPullback_pullback T.B f) hM hM₂ ((isGen_iff u).1 hu) hK
  refine ⟨torusExtOfIso e (teBC f T), M.pull (pullback.fst T.B.hom f), hM₂, hK₂, ?_⟩
  have hc : (e.inv ≫ Out.GtBCPf.qB f T.q).left ≫ pullback.fst T.B.hom f = φ ≫ T.q.left := by
    rw [Over.comp_left, Category.assoc, Out.GtBCPf.qB_h, ← hφ, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      e.inv_hom_id, Over.id_left, Category.id_comp]
  exact LBIso.trans hL₂ (pull_isLB hL φ) (pull_isLB hM₂ _) w
    (LBIso.chartPull (chartPullPull L φ φ rfl) (chartPullLinComb M (pullback.fst T.B.hom f)
      (fun _ : PUnit => (e.inv ≫ Out.GtBCPf.qB f T.q).left) (fun _ => T.q.left) (fun _ => 1) φ fun _ => hc) hi)

theorem geompf_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), (∀ (k k₂ : Type) [Field k] [Field k₂] (f : k →+* k₂) (x : Sp k ⟶ X0), GeomPF t x → GeomPF t (spMap f ≫ x)) ∧ ∀ (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (k : Type) [Field k] (x : Sp k ⟶ X₂), GeomPF t₂ x ↔ GeomPF t (x ≫ f) := by
  intro E _ _ _ H X0 t
  have hL := t.PP.isLB
  refine ⟨fun k k₂ _ _ f x h => ?_, fun X₂ t₂ f m k _ x => ?_⟩
  · let φ : pullback t.G.hom (spMap f ≫ x) ⟶ pullback t.G.hom x :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f) (by rw [Category.assoc, pullback.condition])
    have e : φ ≫ pullback.fst t.G.hom x = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hg : IsGrpPullback ((Over.pullback (spMap f ≫ x)).obj t.G) ((Over.pullback x).obj t.G) (spMap f) φ :=
      (isGrpPullback_pullback t.G x).cancel ((isGrpPullback_pullback t.G _).congr rfl e.symm) (pullback.lift_snd _ _ _)
    exact pf_pull (spMap f) hg (pull_isLB hL _) (pull_isLB hL _) (lbIso_pull_pull hL _ φ _ e) h
  · have hL₂ := t₂.PP.isLB
    have h₁ := (isGrpPullback_pullback t₂.G x).comp m.cart
    have h₂ := isGrpPullback_pullback t.G (x ≫ f)
    obtain ⟨w, hw, -⟩ := m.lin
    have w₁ : LBIso (t₂.PP.L.pull (pullback.fst t₂.G.hom x)) ((t.PP.L.pull m.cm.F).pull (pullback.fst t₂.G.hom x)) :=
      LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) ⟨w, hw⟩
    have w₂ := LBIso.trans (pull_isLB hL₂ _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) w₁
      (lbIso_pull_pull hL m.cm.F (pullback.fst t₂.G.hom x) _ rfl).symm
    constructor
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₂ h₁
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (pull_isLB hL₂ _) (pull_isLB hL _) ?_ h
      refine LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL₂ _) _)
        (lbIso_pull_pull hL _ e.hom.left _ hφ) ?_
      exact LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) w₂.symm
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁ h₂
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (pull_isLB hL _) (pull_isLB hL₂ _) ?_ h
      exact LBIso.trans (pull_isLB hL₂ _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) w₂
        (lbIso_pull_pull hL _ e.hom.left _ hφ)

theorem exists_common {X₂ X0 : Scheme.{0}} (f : X₂ ⟶ X0) (z : X₂) {k : Type} [Field k] (x : Sp k ⟶ X0)
    (hx : x (IsLocalRing.closedPoint k) = f z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ X₂) (a : k →+* Ω),
      y (IsLocalRing.closedPoint Ω) = z ∧ y ≫ f = spMap a ≫ x := by
  obtain ⟨s, hs, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := x) z _ hx.symm
  let P := pullback f x
  let Ω := AlgebraicClosure (P.residueField s)
  let r : Sp Ω ⟶ P := spMap (algebraMap (P.residueField s) Ω) ≫ P.fromSpecResidueField s
  have hr : r (IsLocalRing.closedPoint Ω) = s := Scheme.fromSpecResidueField_apply s _
  refine ⟨Ω, inferInstance, inferInstance, r ≫ pullback.fst f x, (Spec.preimage (r ≫ pullback.snd f x)).hom, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (pullback.fst f x) hr).trans hs)
  · show _ = Spec.map (Spec.preimage (r ≫ pullback.snd f x)) ≫ x
    rw [Spec.map_preimage, Category.assoc r, Category.assoc r, pullback.condition]

theorem fibpf_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  intro E _ _ _ H X0 t X₂ t₂ f m z
  constructor
  · rintro ⟨k, _, _, x, rfl, h⟩
    exact ⟨k, _, inferInstance, x ≫ f, Scheme.Hom.comp_apply _ _ _, ((geompf_bc E H X0 t).2 X₂ t₂ f m k x).1 h⟩
  · rintro ⟨k, _, _, x, hx, h⟩
    obtain ⟨Ω, _, _, y, a, hy, e⟩ := exists_common f z x hx
    exact ⟨Ω, _, inferInstance, y, hy,
      ((geompf_bc E H X0 t).2 X₂ t₂ f m Ω y).2 (e ▸ (geompf_bc E H X0 t).1 k Ω a x h)⟩

end PositivityTheory.HtPt.Cf
