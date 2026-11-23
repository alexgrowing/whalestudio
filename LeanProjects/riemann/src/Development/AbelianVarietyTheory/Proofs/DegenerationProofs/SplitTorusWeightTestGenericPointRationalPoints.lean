import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

def wtDefect {P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens) (u : Γ(G, V))
    (e : Γ(T, ⊤)) : Γ(P, a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) :=
  (a.appLE V _ inf_le_left).hom u - (c.appLE ⊤ _ le_top).hom e * (b.appLE V _ inf_le_right).hom u

theorem appLE_wtDefect {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by
  subst ha hb hc
  have e₁ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p a V _ ⊤ inf_le_left h)
  have e₂ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p b V _ ⊤ inf_le_right h)
  have e₃ := congrArg (fun q => CommRingCat.Hom.hom q e)
    ((Scheme.Hom.appLE_comp_appLE p c ⊤ _ ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (p ≫ c)))
  rw [wtDefect, map_sub, map_mul]
  exact congrArg₂ (· - ·) e₁ (congrArg₂ (· * ·) e₃ e₂)

theorem eq_zero_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced (S := Spec (.of k)) P.hom
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec (.of k)) P.hom
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  have hne' : ((P.left.basicOpen d : P.left.Opens) : Set P.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h' => hne (TopologicalSpace.Opens.ext h')
  obtain ⟨x, hxd, hx⟩ := nonempty_inter_closedPoints hne' (P.left.basicOpen d).isOpen.isLocallyClosed
  refine h (Over.homMk (pointOfClosedPoint (K := k) P.hom x hx)
    (pointOfClosedPoint_comp (K := k) P.hom x hx)) (IsLocalRing.closedPoint k) ?_
  have e := pointOfClosedPoint_apply (K := k) P.hom x hx (IsLocalRing.closedPoint k)
  exact e.symm ▸ hxd

theorem wt_of_genericPoint :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  intro k _ _ G _ hG X _ _ _ i F _ s g hg V u χ H
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp k)).1 X
  have : Smooth (splitTorus (Sp k) X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus (Sp k) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp k) X).hom G.hom ≫
      (splitTorus (Sp k) X).hom))
  have hact : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left = ((t ≫ i) * y).left := by
    intro Z t y
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hsnd : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (snd (splitTorus (Sp k) X) G).left = y.left := by
    intro Z t y
    rw [← Over.comp_left, lift_snd]
  have hfst : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (fst (splitTorus (Sp k) X) G).left = t.left := by
    intro Z t y
    rw [← Over.comp_left, lift_fst]
  have hd : wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val = 0 := by
    refine eq_zero_of_rationalPoints _ fun z x hx => ?_
    set d := wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val with hdd
    let t := z ≫ fst _ _
    let m : G ⟶ splitTorus (Sp k) X ⊗ G := lift (toUnit G ≫ t) (𝟙 G)
    have hz : (z ≫ snd _ _) ≫ m = z := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, t, Category.assoc, lift_fst]
        rw [← Category.assoc (snd _ _), ← Category.assoc z, toUnit_unique (z ≫ _) (𝟙 _),
          Category.id_comp]
      · simp [m]
    have hgm : g ≫ m = lift (toUnit (Over.mk s) ≫ t) g := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, Category.assoc, lift_fst]
        rw [← Category.assoc, toUnit_unique (g ≫ _) (toUnit _)]
      · simp [m]
    have h0 := hg (m.left ⁻¹ᵁ (splitTorus (Sp k) X ⊗ G).left.basicOpen d)
      ⟨(z ≫ snd _ _).left x, by
        have : m.left ((z ≫ snd _ _).left x) = z.left x := congrArg (fun q => q.left x) hz
        show m.left ((z ≫ snd _ _).left x) ∈ (splitTorus (Sp k) X ⊗ G).left.basicOpen d
        rw [this]; exact hx⟩
    have h1 : ⊤ ≤ (lift (toUnit (Over.mk s) ≫ t) g).left ⁻¹ᵁ
        (splitTorus (Sp k) X ⊗ G).left.basicOpen d := by
      rw [← hgm]; exact h0
    have h2 := h1.trans ((lift (toUnit (Over.mk s) ≫ t) g).left.preimage_mono
      ((splitTorus (Sp k) X ⊗ G).left.basicOpen_le d))
    have h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V := by
      rw [← hact]; exact fun y hy => (h2 hy).1
    have h₂ : ⊤ ≤ g.left ⁻¹ᵁ V := by
      rw [← hsnd (toUnit (Over.mk s) ≫ t)]; exact fun y hy => (h2 hy).2
    have hu := isUnit_ev (R := F) _ _ h2 d h1
    have hv := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact _ _) (hsnd _ _) (hfst _ _) h2 h₁ h₂)
    have hH := (H t h₁ h₂).trans (congrArg (· * ev (R := F) g.left V h₂ u)
      (ev_top (R := F) (toUnit (Over.mk s) ≫ t).left le_top (charUnit (Sp k) X χ).val))
    refine hu.ne_zero (hv.trans ?_)
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hH.trans (map_mul _ _ _).symm))
  intro Z t y h₁ h₂
  have h : ⊤ ≤ (lift t y).left ⁻¹ᵁ (((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left ⁻¹ᵁ V ⊓
      (snd (splitTorus (Sp k) X) G).left ⁻¹ᵁ V) := by
    rw [← hact] at h₁
    rw [← hsnd t] at h₂
    exact fun w hw => ⟨h₁ hw, h₂ hw⟩
  have hv := appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact t y) (hsnd t y) (hfst t y)
    h h₁ h₂
  rw [hd, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

end GlobalTheory.SS.WtRat
end
