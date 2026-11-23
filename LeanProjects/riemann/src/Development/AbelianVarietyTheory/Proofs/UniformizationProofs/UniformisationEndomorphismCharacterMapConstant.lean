import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Acts (g : GtCoord I D e G) (a : (thickObj R I e G).left ⟶ (thickObj R I e G).left)
    (f : D.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
    Good D.P.L z J → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    ∀ x, val (g.t x) (r ≫ a) z J = val (g.t (f x)) r z J

theorem acts_of_torusEndOf (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G)
    {f : D.X → D.X} {t : splitTorus _ D.X ⟶ splitTorus _ D.X} (ht : TorusEndOf D.X f t)
    (hi : g.i ≫ a = t ≫ g.i) : Acts g a.left f := by
  intro Z r z J hJ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let b : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g b).2 h)
  have hτ : τ ≫ g.i = b := g.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ t) 1 z J hJ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm τ 1 z J hJ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((EndTorus.torusEndOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g : GtCoord I D e G)
    {a : (thickObj R I e G).left ⟶ (thickObj R I e G).left} {f f' : D.X → D.X}
    (h : Acts g a f) (h' : Acts g a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J hJ c x).symm.trans (h' _ _ z J hJ c x)).trans (k _))

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in

theorem thickMap_comm (aG : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (aG : G ⟶ G) {f : D.toPre.X → D.toPre.X}
    (h : Acts (U.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J hJ c x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J hJ up x
  have sq : (r ≫ thickMap R I e G) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ (U.gt_t e x) _).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e (f x)) r))))

end EndConst

open EndConst in

theorem unifPre_end_character_const : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (aG : G ⟶ G), IsMonHom aG → ∃ h : D.toPre.X →+ D.toPre.X, ∀ e, ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X, TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map aG = t ≫ (U.gt e).i := by
  intro hL R _ _ I hR D A G _ _ U aG haG
  have ex := fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).1.exists
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D.toPre.X → D.toPre.X),
      Acts (U.gt e) ((Over.pullback (thick R I e)).map aG).left f →
      Acts (U.gt 0) ((Over.pullback (thick R I 0)).map aG).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U aG k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ (down e _ (acts_of_torusEndOf _ _ (ht e) (hi e)))
    (acts_of_torusEndOf _ _ (ht 0) (hi 0))]
  exact ht e

end GlobalTheory
