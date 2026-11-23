import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt

noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T T' : Over (Spec (CommRingCat.of R))}

variable {U} in
theorem hasCoords_pull {e : ℕ} {k : T' ⟶ T} {g : GtPt D.toPre T} {g' : GtPt D.toPre T'}
    (h : GtPt.IsPull k.left g g') {Z : Scheme.{0}} {r : Z ⟶ T'.left} {y : Z ⟶ (thickObj R I e G).left} :
    HasCoords U e g (r ≫ k.left) y ↔ HasCoords U e g' r y := by
  rw [hasCoords_iff, hasCoords_iff, h.1, Category.assoc]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun z => forall_congr' fun J =>
    forall_congr' fun hJ => ?_)
  rw [(val_corr hJ (h.2 χ) r).trans (val_pull hJ _ _ _)]

variable {U} in
theorem eq_of_hasCoords {e : ℕ} {g g' : GtPt D.toPre T} {y : T.left ⟶ (thickObj R I e G).left}
    (h : HasCoords U e g (𝟙 _) y) (h' : HasCoords U e g' (𝟙 _) y) : g = g' := by
  rw [hasCoords_iff, Category.id_comp] at h h'
  exact pt_ext (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ z J hJ => (h.2 χ z J hJ).symm.trans (h'.2 χ z J hJ)

theorem isPointOf_iff_thick (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (thickι I e T) (thickHom I e x) := by
  refine ⟨fun h e => h e _ _ _ (thickHom_ι I e x), fun h e Z r y hy => ?_⟩
  have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ thickι I e T = r := ⟨pullback.lift r _ w, pullback.lift_fst _ _ _⟩
  obtain rfl : y = l ≫ thickHom I e x := by
    rw [← cancel_mono (thickι I e G), Category.assoc, thickHom_ι]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

theorem existsUnique_point (hT : IsAdicColimit I T) (g : GtPt D.toPre T) : ∃! x : T ⟶ G, IsPointOf U g x := by
  choose y hy using fun e =>
    exists_hasCoords U e g (thickι I e T) (thickObj R I e T).hom pullback.condition.symm
  refine existsUnique_of_exists_of_unique ?_ fun x x' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    (h.comp_fstG_eq (hy e)).symm.trans (h'.comp_fstG_eq (hy e)))
  obtain ⟨x, hx, -⟩ := hT G.left (fun e => y e ≫ thickι I e G) fun e => by
    have h₁ := (hy (e + 1)).comp (thickMap R I e T)
    rw [thickMap_ι] at h₁
    rw [← Category.assoc, h₁.unique (hy e).succ, Category.assoc, thickMap_ι]
  have hw : x ≫ G.hom = T.hom := hT.hom_ext fun e => by
    have h₁ : thickι I e G ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    rw [reassoc_of% hx e, h₁, reassoc_of% (hy e).1, Over.w]
  refine ⟨Over.homMk x hw, (isPointOf_iff_thick U g _).2 fun e => ?_⟩
  have : thickHom I e (Over.homMk x hw : T ⟶ G) = y e := by
    rw [← cancel_mono (thickι I e G), thickHom_ι]
    exact hx e
  rw [this]
  exact hy e

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T}

theorem existsUnique_lift (hΦ : Represents Φ) (hT : IsAdicColimit I T) (x : T ⟶ G) :
    ∃! w : T ⟶ H, IsPointOf U (Φ T w) x := by
  have pl : ∀ (e : ℕ) (w : T ⟶ H), HasCoords U e (Φ T w) (thickι I e T) (thickHom I e x) ↔
      HasCoords U e (Φ _ (fstG I e T ≫ w)) (𝟙 _) (thickHom I e x) := fun e w => by
    rw [← hasCoords_pull (hΦ.1 _ _ (fstG I e T) w), Category.id_comp]; rfl
  refine existsUnique_of_exists_of_unique ?_ fun w w' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    congrArg (·.left) ((Φ _).injective (eq_of_hasCoords ((pl e w).1 ((isPointOf_iff_thick U _ x).1 h e))
      ((pl e w').1 ((isPointOf_iff_thick U _ x).1 h' e)))))
  have ex : ∀ e, ∃ w : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶ H,
      HasCoords U e (Φ _ w) (𝟙 _) (thickHom I e x) := fun e => by
    obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (U.gt e) (T := (Over.map (thick R I e)).obj (thickObj R I e T))
      (thickHom I e x) (by rw [← Category.assoc, Over.w]; rfl)
    refine ⟨(Φ _).symm ξ, ?_⟩
    rw [Equiv.apply_symm_apply, hasCoords_iff]
    refine ⟨hξ.1.symm.trans (Category.id_comp _).symm, fun χ z J hJ => ?_⟩
    have := (val_corr hJ (hξ.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  choose w hw using ex
  obtain ⟨v, hv, -⟩ := hT H.left (fun e => (w e).left) fun e => by
    let m : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶
        (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) T) := Over.homMk (thickMap R I e T)
      (((congrArg (thickMap R I e T ≫ ·) (Over.w (fstG I (e + 1) T)).symm).trans
        (thickMap_ι_assoc I e T T.hom)).trans (Over.w (fstG I e T)))
    have h₁ := (hw (e + 1)).comp (thickMap R I e T)
    rw [thickMap_thickHom, Category.comp_id, ← Category.id_comp (thickMap R I e T)] at h₁
    have h₂ := (hasCoords_pull (hΦ.1 _ _ m (w (e + 1)))).1 h₁
    exact congrArg (·.left) ((Φ _).injective (eq_of_hasCoords h₂ (hw e).succ))
  have hv' : v ≫ H.hom = T.hom := hT.hom_ext fun e => by
    rw [reassoc_of% hv e, Over.w]
    exact (Over.w (fstG I e T)).symm
  refine ⟨Over.homMk v hv', (isPointOf_iff_thick U _ x).2 fun e => (pl e _).2 ?_⟩
  have : fstG I e T ≫ (Over.homMk v hv' : T ⟶ H) = w e := Over.OverMorphism.ext (hv e)
  rw [this]
  exact hw e

theorem exists_mulEquiv (hG : GlobalFnsSt) (hΦ : Represents Φ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)),
      ∀ T hT w x, J T hT w = x ↔ IsPointOf U (Φ T w) x := by
  choose j hj hu using fun T (hT : IsAdicColimit I T) (w : T ⟶ H) => existsUnique_point U hT (Φ T w)
  have bij : ∀ T hT, Function.Bijective (j T hT) := fun T hT => (Function.bijective_iff_existsUnique _).2 fun x =>
    (existsUnique_congr fun w => ⟨fun h => (hu T hT w x h).symm, fun h => h ▸ hj T hT w⟩).1
      (existsUnique_lift U hΦ hT x)
  exact ⟨fun T hT => MulEquiv.mk' (Equiv.ofBijective _ (bij T hT)) fun w w' =>
      (hu T hT _ _ ((hj T hT w).mul hG (hj T hT w') (hΦ.2 T w w'))).symm,
    fun T hT w x => ⟨fun h => h ▸ hj T hT w, fun h => (hu T hT w x h).symm⟩⟩

end GlobalTheory.TorusModel
