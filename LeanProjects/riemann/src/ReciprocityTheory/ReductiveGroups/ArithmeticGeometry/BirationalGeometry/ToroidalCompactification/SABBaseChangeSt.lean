import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Transport

variable {K : Type} [Field K] {G₁ G₂ : Over (Spec (CommRingCat.of K))} [GrpObj G₁] [GrpObj G₂]

omit [GrpObj G₁] [GrpObj G₂] in
lemma isIso_inv_left (e : G₁ ≅ G₂) : IsIso e.inv.left :=
  Functor.map_isIso (Over.forget _) e.inv

def torusExtOfIso (e : G₁ ≅ G₂) [IsMonHom e.hom] (T : TorusExtension G₁) : TorusExtension G₂ :=
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := T.B
    grpB := T.grpB
    isAbelian := T.isAbelian
    q := e.inv ≫ T.q
    q_hom := inferInstance
    q_flat := by rw [Over.comp_left]; have := T.q_flat; have := isIso_inv_left e; infer_instance
    q_surjective := by rw [Over.comp_left]; have := T.q_surjective; have := isIso_inv_left e; infer_instance
    q_quasiCompact := by rw [Over.comp_left]; have := T.q_quasiCompact; have := isIso_inv_left e; infer_instance
    i := T.i ≫ e.hom
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso T.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }

end Transport

section Pull

variable {T S S' : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G]

def pullCompMon : (Over.pullback (p ≫ f)).mapMon.obj (Mon.mk G) ≅
    (Over.pullback p).mapMon.obj ((Over.pullback f).mapMon.obj (Mon.mk G)) :=
  (Functor.mapMonNatIso (Over.pullbackComp p f) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)

def pullCompIso : (Over.pullback (p ≫ f)).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G) :=
  (Mon.forget _).mapIso (pullCompMon p f G)

instance : IsMonHom (pullCompIso p f G).hom := by
  show IsMonHom (pullCompMon p f G).hom.hom
  infer_instance

theorem IsSemiAbelian.pullback (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) where
  comm := by have := h.comm; infer_instance
  smooth := by have := h.smooth; show Smooth (pullback.snd G.hom f); infer_instance
  separated := by have := h.separated; show IsSeparated (pullback.snd G.hom f); infer_instance
  quasiCompact := by have := h.quasiCompact; show QuasiCompact (pullback.snd G.hom f); infer_instance
  geomConnected := by have := h.geomConnected; show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  fibres := fun Ω _ _ q => by
    obtain ⟨E⟩ := h.fibres Ω (q ≫ f)
    exact ⟨torusExtOfIso (pullCompIso q f G) E⟩

def OAct.pullback [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G) : OAct O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

end Pull

def SABBaseChangeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (PP' : RigLB ((Over.pullback f).obj t.G)),
    (∃ w : LB.Iso PP'.L (t.PP.L.pull (pullback.fst t.G.hom f)), w.IsGen) →
    ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
      (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
      (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
        (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
      (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L)),
      Nonempty (SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
