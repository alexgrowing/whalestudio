import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.Vert.DivPull

section Sections

variable {X Y Y' W : Scheme.{0}}

theorem pullbackComp_inv_app (b : W ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).inv.app E).app T (pullbackSections (b ≫ a) E h s) =
      pullbackSections b _ h₂ (pullbackSections a E h₁ s) := by
  have e := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)) (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at e
  refine (app_resM _ h _).trans (Eq.trans ?_ (pullbackSections_res b _ h₂ h₁ _).symm)
  exact congrArg (resM _ h) congr(($e).app U s).symm

theorem pullbackSquare_app {b : W ⟶ Y} {a : Y ⟶ X} {b' : W ⟶ Y'} {a' : Y' ⟶ X}
    (w : b ≫ a = b' ≫ a') (E : X.Modules) {U : X.Opens} {V : Y.Opens} {V' : Y'.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h₁' : V' ≤ a' ⁻¹ᵁ U) (h₂' : T ≤ b' ⁻¹ᵁ V')
    (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp b' a').symm).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections b' _ h₂' (pullbackSections a' E h₁' s) := by
  have H {j j' : W ⟶ X} (w : j = j') (h : T ≤ j ⁻¹ᵁ U) (h' : T ≤ j' ⁻¹ᵁ U) :
      ((Scheme.Modules.pullbackCongr w).hom.app E).app T (pullbackSections j E h s) =
        pullbackSections j' E h' s := by
    subst w; rfl
  have h : T ≤ (b ≫ a) ⁻¹ᵁ U := h₂.trans (b.preimage_mono h₁)
  have h' : T ≤ (b' ≫ a') ⁻¹ᵁ U := h₂'.trans (b'.preimage_mono h₁')
  rw [← pullbackComp_inv_app b a E h₁ h₂ h, ← pullbackComp_inv_app b' a' E h₁' h₂' h',
    ← H w h h']
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫
      (Scheme.Modules.pullbackComp b' a').symm).hom.app E =
      (Scheme.Modules.pullbackCongr w).hom.app E ≫ (Scheme.Modules.pullbackComp b' a').inv.app E := by
    simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

theorem detUnit_congr {F : X.Modules} {r : ℕ} {U U' T T' V : X.Opens} {e : Fin r → Γ(F, U)}
    {e' : Fin r → Γ(F, U')} {d : Fin r → Γ(F, T)} {d' : Fin r → Γ(F, T')} (he : IsFrame e)
    (he' : IsFrame e') (hd : IsFrame d) (hd' : IsFrame d') (h : V ≤ U) (h' : V ≤ U') (k : V ≤ T)
    (k' : V ≤ T') (H : ∀ i, resM F h (e i) = resM F k (d i))
    (H' : ∀ i, resM F h' (e' i) = resM F k' (d' i)) :
    he.detUnit he' h h' = hd.detUnit hd' k k' := by
  have e₁ : he.basis h = hd.basis k :=
    DFunLike.ext _ _ fun i => by simp only [IsFrame.basis_apply, H]
  refine Units.ext ?_
  simp only [IsFrame.val_detUnit, e₁, H']

theorem app_app_eq {A B C D : X.Modules} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D}
    (e : a ≫ b = c ≫ d) (T : X.Opens) (s : Γ(A, T)) : b.app T (a.app T s) = d.app T (c.app T s) :=
  congr(($e).app T s)

end Sections

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z Z₁ : Model O}
  {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules} {r : ℕ}

def pullChart {X Y : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (c : Chart F r) (g : Y ⟶ X) :
    Chart ((Scheme.Modules.pullback g).obj F) r :=
  ⟨g ⁻¹ᵁ c.U, _, c.isFrame.pullback g⟩

theorem val_detUnit_pull [E.IsQuasicoherent] [E'.IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj E).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj E').IsQuasicoherent] [(Z.genRes.obj E).IsQuasicoherent]
    (φ : Z.GenIso E E') (c : Chart E r) (c' : Chart E' r) {V : Z.gen.toScheme.Opens}
    (hV : V ≤ Z.gen.ι ⁻¹ᵁ (c.U ⊓ c'.U)) {T : Z₁.gen.toScheme.Opens}
    (h : T ≤ Z₁.gen.ι ⁻¹ᵁ ((pullChart c f).U ⊓ (pullChart c' f).U))
    (hT : T ≤ GenIso.genMap hf ⁻¹ᵁ V) :
    ((φ.pull hf).detUnit (pullChart c f) (pullChart c' f) h).val =
      ((GenIso.genMap hf).appLE V T hT).hom (φ.detUnit c c' hV).val := by
  rw [GenIso.detUnit, GenIso.detUnit, ← IsFrame.val_detUnit_pullback,
    ← IsFrame.detUnit_map_iso _ _ ((GenIso.genPullIso hf).hom.app E)]
  refine congrArg Units.val (detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) fun i => ?_)
  · refine (app_resM _ _ _).symm.trans (Eq.trans ?_ (res_pullbackSections _ _ _ _ _).symm)
    refine (congrArg _ (res_pullbackSections _ _ _ _ _)).trans ?_
    exact pullbackSquare_app _ E _ _ _ _ _
  · have e : (φ.pull hf).inv ≫ (GenIso.genPullIso hf).hom.app E =
        (GenIso.genPullIso hf).hom.app E' ≫
          (Scheme.Modules.pullback (GenIso.genMap hf)).map φ.inv := by
      simp [GenIso.pull]
    refine (app_resM _ _ _).symm.trans (Eq.trans ?_ (res_pullbackSections _ _ _ _ _).symm)
    refine (congrArg _ (app_resM _ _ _).symm).trans ?_
    refine Eq.trans ?_ (pullback_map_app_pullbackSections _ _ _ _)
    refine (app_app_eq e T _).trans (congrArg _ ?_)
    refine (congrArg _ (res_pullbackSections _ _ _ _ _)).trans ?_
    exact pullbackSquare_app _ E' _ _ _ _ _

theorem cls_div_pull (hE : IsVB E r) (hE' : IsVB E' r) (φ : Z.GenIso E E') :
    ((φ.pull hf).div (hE.pullback f) (hE'.pullback f)).cls = vPull hf (φ.div hE hE').cls := by
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  have := (hE.pullback f).isQuasicoherent
  have := (hE'.pullback f).isQuasicoherent
  have := (hE.pullback Z.gen.ι).isQuasicoherent
  rw [← VertDiv.cls_pull, ← add_zero ((φ.div hE hE').pull hf).cls, ← VertDiv.cls_zero Z₁]
  refine VertDiv.IsSum.cls_eq fun i j k => ?_
  let p : ((φ.pull hf).div (hE.pullback f) (hE'.pullback f)).M.ι :=
    (pullChart (i ⟨⟩).1 f, pullChart (i ⟨⟩).2 f)
  have hp : ((φ.div hE hE').pull hf).M.U i ≤
      ((φ.pull hf).div (hE.pullback f) (hE'.pullback f)).M.U p := LB.pull_U_le f i
  have key {W : Z₁.X.Opens} (hW : W ≤ Z₁.gen ⊓ ((φ.div hE hE').pull hf).M.U i) :
      ((φ.pull hf).div (hE.pullback f) (hE'.pullback f)).eqn p (hW.trans (inf_le_inf_left _ hp)) =
        ((φ.div hE hE').pull hf).eqn i hW := by
    have hW' : W ≤ f ⁻¹ᵁ (Z.gen ⊓ ((i ⟨⟩).1.U ⊓ (i ⟨⟩).2.U)) :=
      hW.trans (inf_le_inf (preimage_gen hf).ge hp)
    have e : ((φ.div hE hE').pull hf).eqn i hW =
        (f.appLE _ _ hW').hom ((φ.div hE hE').eqn (i ⟨⟩) le_rfl) := by
      change resG Z₁.X _ (resG Z₁.X _ ((f.appLE _ _ (LB.pull_inf_le f _ i)).hom _)) = _
      rw [LB.resG_appLE, LB.resG_appLE, VertDiv.eqn]
      exact (LB.appLE_resG _ _ _ _).symm
    have w : GenIso.genMap hf ≫ Z.gen.ι = Z₁.gen.ι ≫ f := f.resLE_comp_ι (preimage_gen hf).ge
    have hT : Z₁.gen.ι ⁻¹ᵁ W ≤ GenIso.genMap hf ⁻¹ᵁ Z.gen.ι ⁻¹ᵁ
        (Z.gen ⊓ ((i ⟨⟩).1.U ⊓ (i ⟨⟩).2.U)) := by
      rw [← Scheme.Hom.comp_preimage, w]
      exact Z₁.gen.ι.preimage_mono hW'
    refine (genEquiv (hW.trans inf_le_left)).injective ?_
    refine (GenIso.genEquiv_eqn_div _ _ _ _ _ _).trans ?_
    rw [val_detUnit_pull hf φ _ _ (Z.gen.ι.preimage_mono inf_le_right) _ hT, e,
      ← GenIso.genEquiv_eqn_div φ hE hE' _ _ le_rfl, genEquiv_apply, genEquiv_apply]
    have e₁ := Scheme.Hom.comp_appLE (GenIso.genMap hf) Z.gen.ι
      (Z.gen ⊓ ((i ⟨⟩).1.U ⊓ (i ⟨⟩).2.U)) _ hT
    have e₂ := Scheme.Hom.appLE_comp_appLE Z₁.gen.ι f _ _ _ hW' le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at e₂
    have e₃ : ∀ {j j' : Z₁.gen.toScheme ⟶ Z.X} (_ : j = j') (U V h h'),
      j.appLE U V h = j'.appLE U V h' := by rintro _ _ rfl _ _ _ _; rfl
    exact congr(($(e₁.symm.trans ((e₃ w _ _ _ _).trans e₂.symm))).hom _)
  refine ⟨res (le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans hp)))
    (((φ.pull hf).div (hE.pullback f) (hE'.pullback f)).M.g k p), ?_⟩
  rw [← key, LB.val_res, LB.resG_resG]
  refine (VertDiv.eqn_rel _ k p _ (inf_le_inf_left _ (inf_le_left.trans (inf_le_left.trans hp)))
    _).trans (congrArg _ ?_)
  exact (mul_one _).symm.trans (congrArg _ (map_one _).symm)

end GlobalTheory.Vert.DivPull
