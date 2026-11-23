import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem UpperTheory.appLE_injective_of_dominant {Z P : Scheme.{0}} [IsReduced P] (p : Z ⟶ P) [IsDominant p] (W : P.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ W) (A B : Γ(P, W)) (e : (p.appLE W ⊤ h).hom A = (p.appLE W ⊤ h).hom B) : A = B := by
  have e0 : (p.appLE W ⊤ h).hom (A - B) = 0 := by rw [map_sub, e, sub_self]
  have e1 := Scheme.basicOpen_appLE p ⊤ W h (A - B)
  rw [show p.appLE W ⊤ h (A - B) = 0 from e0, Scheme.basicOpen_zero, top_inf_eq] at e1
  refine sub_eq_zero.1 (eq_zero_of_basicOpen_eq_bot _ ?_)
  by_contra hne
  obtain ⟨z, hz⟩ := p.denseRange.exists_mem_open (P.basicOpen (A - B)).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have : z ∈ p ⁻¹ᵁ P.basicOpen (A - B) := hz
  rw [← e1] at this
  exact this

private theorem UpperTheory.appLE_appLE_eq_appLE_of_comp {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) (c : Z ⟶ Y) (e : p ≫ a = c)
    (V : Y.Opens) (W : P.Opens) (hW : W ≤ a ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ W) (h' : ⊤ ≤ c ⁻¹ᵁ V) (f : Γ(Y, V)) :
    (p.appLE W ⊤ h).hom ((a.appLE V W hW).hom f) = (c.appLE V ⊤ h').hom f := by
  subst e
  exact congrArg (fun q => q.hom f) (Scheme.Hom.appLE_comp_appLE p a V W ⊤ hW h)

private theorem UpperTheory.appLE_product_iff {Z P T G : Scheme.{0}} (a s : P ⟶ G) (r : P ⟶ T) (V : G.Opens) (f : Γ(G, V))
    (c : Γ(T, ⊤)) (p : Z ⟶ P) (a' s' : Z ⟶ G) (r' : Z ⟶ T) (ea : p ≫ a = a') (es : p ≫ s = s') (er : p ≫ r = r')
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ s' ⁻¹ᵁ V) :
    ∃ h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V),
      ((p.appLE _ ⊤ h).hom ((a.appLE V _ inf_le_left).hom f) =
        (p.appLE _ ⊤ h).hom ((r.appLE ⊤ _ le_top).hom c * (s.appLE V _ inf_le_right).hom f) ↔
      (a'.appLE V ⊤ h₁).hom f = r'.appTop.hom c * (s'.appLE V ⊤ h₂).hom f) := by
  have h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) := by
    subst ea es
    exact fun z hz => ⟨h₁ hz, h₂ hz⟩
  refine ⟨h, ?_⟩
  rw [map_mul, UpperTheory.appLE_appLE_eq_appLE_of_comp p a a' ea V _ _ h h₁, UpperTheory.appLE_appLE_eq_appLE_of_comp p s s' es V _ _ h h₂]
  have e3 := UpperTheory.appLE_appLE_eq_appLE_of_comp p r r' er ⊤ _ le_top h le_top c
  have : r'.appLE ⊤ ⊤ le_top = r'.appTop := (Scheme.Hom.app_eq_appLE r' (U := ⊤)).symm
  rw [this] at e3
  exact Eq.congr_right (congrArg (· * (s'.appLE V ⊤ h₂).hom f) e3)

theorem UpperTheory.wt_generic :
    WtGeneric := by
  intro S G _ X _ u hint V f χ Z t g hdom h₁ h₂ H Z' t' g' h₁' h₂'
  have key : ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ G),
      (lift t g).left ≫ ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G).left = ((t ≫ u) * g).left ∧
      (lift t g).left ≫ (snd (splitTorus S X) G).left = g.left ∧
      (lift t g).left ≫ (fst (splitTorus S X) G).left = t.left := fun Y t g => by
    refine ⟨?_, ?_, ?_⟩
    · rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
    · rw [← Over.comp_left, lift_snd]
    · rw [← Over.comp_left, lift_fst]
  obtain ⟨a, b, c⟩ := key Z t g
  obtain ⟨a', b', c'⟩ := key Z' t' g'
  obtain ⟨h, e⟩ := UpperTheory.appLE_product_iff _ _ _ V f (charUnit S X χ).val _ _ _ _ a b c h₁ h₂
  obtain ⟨h', e'⟩ := UpperTheory.appLE_product_iff _ _ _ V f (charUnit S X χ).val _ _ _ _ a' b' c' h₁' h₂'
  exact e'.1 (congrArg _ (UpperTheory.appLE_injective_of_dominant _ _ h _ _ (e.2 H)))
