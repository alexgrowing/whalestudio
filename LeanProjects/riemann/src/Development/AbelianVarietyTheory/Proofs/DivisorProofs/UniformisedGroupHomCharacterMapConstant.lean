import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismCharacterMapConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.HomConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

def Acts (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left) (f : D₂.X → D₁.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J₁ : (Z ⟶ D₁.P.A.left) → D₁.P.L.ι)
    (J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D₁.P.L z J₁ → Good D₂.P.L z J₂ →
    r ≫ g₁.pG.left = r ≫ (fstG I e G₁).left ≫ G₁.hom ≫ eSec D₁.P.A →
    ∀ x, val (g₂.t x) (r ≫ a) z J₂ = val (g₁.t (f x)) r z J₁

theorem acts_of_torusHomOf (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) {f : D₂.X → D₁.X}
    {t : splitTorus _ D₁.X ⟶ splitTorus _ D₂.X} (ht : TorusHomOf f t)
    (hi : g₁.i ≫ a = t ≫ g₂.i) : Acts g₁ g₂ a.left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G₁).hom)
  let b : FinalForm ⟶ thickObj R I e G₁ := Over.homMk r rfl
  let τ := g₁.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g₁ b).2 h)
  have hτ : τ ≫ g₁.i = b := g₁.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g₂.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D₂ e G₂ g₂ FinalForm (τ ≫ t) 1 z J₂ hJ₂ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ FinalForm τ 1 z J₁ hJ₁ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((torusHomOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    {a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left} {f f' : D₂.X → D₁.X}
    (h : Acts g₁ g₂ a f) (h' : Acts g₁ g₂ a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J₁ hJ₁ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  choose J₂ hJ₂ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₂.P.A.left => exists_chart D₂.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g₁ g₁.i).1 g₁.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ _ (𝟙 _) 1 z J₁ hJ₁ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J₁ J₂ hJ₁ hJ₂ c x).symm.trans (h' _ _ z J₁ J₂ hJ₁ hJ₂ c x)).trans (k _))

omit [IsDomain R] [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] in

theorem thickMap_comm (aG : G₁ ⟶ G₂) (e : ℕ) :
    thickMap R I e G₁ ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G₂ := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (aG : G₁ ⟶ G₂)
    {f : D₂.toPre.X → D₁.toPre.X}
    (h : Acts (U₁.gt (e + 1)) (U₂.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ c x
  have t : thickMap R I e G₁ ≫ (fstG I (e + 1) G₁).left = (fstG I e G₁).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G₁) ≫ (U₁.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G₁) ≫ (fstG I (e + 1) G₁).left ≫ G₁.hom ≫ eSec D₁.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U₁.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G₁.hom ≫ eSec D₁.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G₁) z J₁ J₂ hJ₁ hJ₂ up x
  have sq : (r ≫ thickMap R I e G₁) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G₂ := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ₂ (U₂.gt_t e x) _).symm.trans ((val_pull hJ₂ _ _ _).trans (k.trans
    ((val_pull hJ₁ _ _ _).symm.trans (val_corr hJ₁ (U₁.gt_t e (f x)) r))))

theorem exists_torus_hom (hR : AdmBase R I) (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ h : D₂.X →+ D₁.X, ∃ t, TorusHomOf h t ∧ g₁.i ≫ a = t ≫ g₂.i := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := EndTorus.connectedSpace_thickening I e
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₂.i_hom
  have hk := g₂.isKernel
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  have : Mono g₂.i := by
    have : Mono (η[thickObj R I e D₂.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  let t := hk.lift (g₁.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
  have ht : t ≫ g₂.i = g₁.i ≫ a := hk.lift_fst _ _ _
  have : IsMonHom (t ≫ g₂.i) := ht ▸ inferInstance
  have : IsMonHom t := EndTorus.isMonHom_of_mono t g₂.i
  obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
  exact ⟨h, t, (torusHomOf_iff_appTop _ _).2 hh, ht.symm⟩

end GlobalTheory.Mum.Two.HomConst

open GlobalTheory.Mum.Two.HomConst in

theorem GlobalTheory.Mum.Two.unifPre_hom_character_const : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have ex := fun e => exists_torus_hom hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D₂.toPre.X → D₁.toPre.X),
      Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a).left f →
      Acts (U₁.gt 0) (U₂.gt 0) ((Over.pullback (thick R I 0)).map a).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U₁ U₂ a k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ _ (down e _ (acts_of_torusHomOf _ _ _ (ht e) (hi e)))
    (acts_of_torusHomOf _ _ _ (ht 0) (hi 0))]
  exact ht e
