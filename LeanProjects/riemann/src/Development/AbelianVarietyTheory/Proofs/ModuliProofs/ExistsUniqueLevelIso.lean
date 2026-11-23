import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Formal
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

local notation "𝔪" => IsLocalRing.maximalIdeal V

omit [IsDomain V] in

instance connectedSpace_level (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (V ⧸ 𝔪 ^ (e + 1)))) :=
  SplitTorus.connectedSpace_of_isLocalRing _

omit [IsDomain V] [GrpObj G] [IsCommMonObj G] in

theorem thickMap_pr (e : ℕ) : thickMap V 𝔪 e G ≫ pr 𝔪 (e + 1) G = pr 𝔪 e G :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain V] in

theorem nonempty_formalTorus (hG : IsSemiAbelian G) (Q₀ : TQ (thickObj V 𝔪 0 G) X) :
    Nonempty (FormalTorus 𝔪 Q₀.i) := by
  have := hG.smooth
  have := hG.geomConnected
  have hs : ∀ e, Smooth (thickObj V 𝔪 e G).hom := fun e => inferInstanceAs (Smooth (pullback.snd _ _))
  have hc : ∀ e, GeometricallyConnected (thickObj V 𝔪 e G).hom := fun e =>
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  have step : ∀ (e : ℕ) (Q : TQ (thickObj V 𝔪 e G) X), ∃ Q' : TQ (thickObj V 𝔪 (e + 1) G) X,
      TorusCompat (thickTrans V _ e) (thickMap V _ e G) Q.i Q'.i := fun e Q => by
    exact exists_tq_lift (TowerEx.isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _
      (TowerEx.isGrpPullback_thickMap 𝔪 e G) Q
  choose nxt hnxt using step
  let Q : ∀ e, TQ (thickObj V 𝔪 e G) X := fun e => Nat.rec (motive := fun e => TQ (thickObj V 𝔪 e G) X) Q₀ nxt e
  exact ⟨⟨fun e => (Q e).i, fun e => (Q e).i_hom, rfl, fun e => hnxt e (Q e)⟩⟩

omit [IsLocalRing V] [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem level_iff {I : Ideal V} {P : CP G} {e : ℕ} {Pe : CP (thickObj V I e G)} (h : IsLevelCP I e Pe P)
    {i : splitTorus (Lv I e) X ⟶ thickObj V I e G} (hi : IsMonHom i) :
    Nonempty (SymTriv P (i.left ≫ pr I e G) (torus_w i)) ↔ ∃ σ : CubTriv Pe.c i, σ.Even := by
  obtain ⟨w, hw⟩ := h
  exact nonempty_symTriv_iff hw _

theorem level_lift (hG : IsSemiAbelian G) {P : CP G} {e : ℕ} {P₁ : CP (thickObj V 𝔪 e G)}
    {P₂ : CP (thickObj V 𝔪 (e + 1) G)} (h₁ : IsLevelCP 𝔪 e P₁ P) (h₂ : IsLevelCP 𝔪 (e + 1) P₂ P)
    {i₁ : splitTorus (Lv 𝔪 e) X ⟶ thickObj V 𝔪 e G} {i₂ : splitTorus (Lv 𝔪 (e + 1)) X ⟶ thickObj V 𝔪 (e + 1) G}
    (m₁ : IsMonHom i₁) (m₂ : IsMonHom i₂) (hi : TorusCompat (thickTrans V 𝔪 e) (thickMap V 𝔪 e G) i₁ i₂)
    (h : ∃ σ : CubTriv P₁.c i₁, σ.Even) : ∃ σ : CubTriv P₂.c i₂, σ.Even := by
  have := hG.smooth
  have := hG.geomConnected
  have hs : Smooth (thickObj V 𝔪 (e + 1) G).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have hc : GeometricallyConnected (thickObj V 𝔪 (e + 1) G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  obtain ⟨_, hP⟩ := TowerEx.exists_isCPMap_thickMap h₁ h₂
  exact exists_even_lift (TowerEx.isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _
    (TowerEx.isGrpPullback_thickMap _ e G) hP hi h

theorem hasSymTriv_iff (hG : IsSemiAbelian G) {P : CP G} {P₀ : CP (thickObj V 𝔪 0 G)} (h₀ : IsLevelCP 𝔪 0 P₀ P)
    {i₀ : splitTorus (Lv 𝔪 0) X ⟶ thickObj V 𝔪 0 G} (F : FormalTorus 𝔪 i₀) :
    F.HasSymTriv P ↔ ∃ σ : CubTriv P₀.c i₀, σ.Even := by
  obtain ⟨i, hom, rfl, compat⟩ := F
  refine Iff.trans ⟨fun ⟨σ, _⟩ => ⟨σ 0⟩, fun h => ?_⟩ (level_iff h₀ (hom 0))
  have all : ∀ e, Nonempty (SymTriv P ((i e).left ≫ pr 𝔪 e G) (torus_w (i e))) := fun e => by
    induction e with
    | zero => exact h
    | succ e ih =>
      obtain ⟨P₁, h₁⟩ := exists_isLevelCP 𝔪 e P
      obtain ⟨P₂, h₂⟩ := exists_isLevelCP 𝔪 (e + 1) P
      exact (level_iff h₂ (hom _)).2 (level_lift hG h₁ h₂ (hom _) (hom _) (compat e) ((level_iff h₁ (hom _)).1 ih))
  have ej : ∀ e, SplitTorus.bcMap (thickTrans V 𝔪 e) X ≫ (i (e + 1)).left ≫ pr 𝔪 (e + 1) G =
      (i e).left ≫ pr 𝔪 e G := fun e => by
    rw [← Category.assoc, torusCompat_iff.1 (compat e), Category.assoc, thickMap_pr]
  exact ⟨fun e => (all e).some, fun e => symTriv_compat (all (e + 1)).some (all e).some (thickTrans_comp V 𝔪 e) (ej e)⟩

theorem symTriv_clause_iff (hG : IsSemiAbelian G) {P : CP G} {P₀ : CP (thickObj V 𝔪 0 G)} (h₀ : IsLevelCP 𝔪 0 P₀ P)
    (Q₀ : TQ (thickObj V 𝔪 0 G) X) :
    (∀ F : FormalTorus 𝔪 Q₀.i, F.HasSymTriv P) ↔ ∃ σ : CubTriv P₀.c Q₀.i, σ.Even :=
  ⟨fun h => (nonempty_formalTorus hG Q₀).elim fun F => (hasSymTriv_iff hG h₀ F).1 (h F),
    fun h F => (hasSymTriv_iff hG h₀ F).2 h⟩

omit [IsLocalRing V] in

theorem existsUnique_level_iso {I : Ideal V} {e : ℕ} [ConnectedSpace (Lv I e)] (Q : TQ (thickObj V I e G) X)
    {P : CP G} {P₁ P₂ : CP (thickObj V I e G)} (h₁ : IsLevelCP I e P₁ P) (h₂ : IsLevelCP I e P₂ P) :
    ∃! w, IsCPMap P₁ P₂ (𝟙 _) (𝟙 _) (by simp) w := by
  obtain ⟨_, h⟩ := h₁
  obtain ⟨_, h'⟩ := h₂
  have : IsMonHom (Iso.refl (thickObj V I e G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨w, hw, -⟩ := cancel_of_eq (isGrpPullback_of_iso (Iso.refl _)) (Category.id_comp _) (Category.id_comp _) h' h
  exact ⟨w, hw, fun _ hv => cp_unique Q hv hw⟩

end Formal

end GlobalTheory.UniformizationSetting
end
