import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.PullAutConst

theorem gm_pullChart {X Z T : Scheme.{0}} (L : LB X) (F : Z ⟶ X) (f : T ⟶ Z) (y : T) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y _ ((L.pull F).g (fun _ => j) (fun _ => j')) = gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem exists_glued {X Y B : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β))
    (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hL : L.IsLB) (hM : M₀.IsLB)
    (hF : PGen wF) (hw : PGen w) (hβ : π₁ ≫ β = π₂ ≫ β) :
    ∃ s : Γ(B, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (j₀ : M₀.ι) (j₁ j₂ : L.ι),
      β (π₁ (f z)) ∈ M₀.U j₀ → π₁ (f z) ∈ L.U j₁ → π₂ (f z) ∈ L.U j₂ →
      gm f z ⊤ s = gw wF (f ≫ π₂) z j₀ j₂ * gw w f z j₂ (fun _ => j₁) * (gw wF (f ≫ π₁) z j₀ j₁)⁻¹ := by
  have hpt : ∀ x, β (π₁ x) = β (π₂ x) := fun x => congrArg (fun g : B ⟶ Y => g x) hβ
  obtain ⟨W, hW⟩ : ∃ W : M₀.ι × L.ι × L.ι → B.Opens, ∀ t x,
      x ∈ W t ↔ β (π₁ x) ∈ M₀.U t.1 ∧ π₁ x ∈ L.U t.2.1 ∧ π₂ x ∈ L.U t.2.2 :=
    ⟨fun t => π₁ ⁻¹ᵁ (β ⁻¹ᵁ M₀.U t.1) ⊓ (π₁ ⁻¹ᵁ L.U t.2.1 ⊓ π₂ ⁻¹ᵁ L.U t.2.2), fun _ _ => Iff.rfl⟩
  have l₂ : ∀ t, W t ≤ π₂ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.2) := fun t x hx =>
    ⟨mem_pull.2 (show β (π₂ x) ∈ _ by rw [← hpt]; exact ((hW t x).1 hx).1), ((hW t x).1 hx).2.2⟩
  have lw : ∀ t, W t ≤ (L.pull π₂).U (fun _ => t.2.2) ⊓ (L.pull π₁).U (fun _ => t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).2.2, mem_pull.2 ((hW t x).1 hx).2.1⟩
  have l₁ : ∀ t, W t ≤ π₁ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).1, ((hW t x).1 hx).2.1⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ t, Γ(B, W t)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t : M₀.ι × L.ι × L.ι), f z ∈ W t →
      gm f z (W t) (u t) =
        gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ :=
    ⟨fun t => res (l₂ t) (pullU π₂ _ (wF.s (fun _ => t.1, t.2.2))) * res (lw t) (w.s (fun _ => t.2.2, fun _ => t.2.1)) *
        (res (l₁ t) (pullU π₁ _ (wF.s (fun _ => t.1, t.2.1))))⁻¹, fun Z f z t hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res f z (l₂ t) hz _).trans (gm_pull f π₂ z _ (l₂ t hz) _)) (gm_res f z (lw t) hz _)))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ t) hz _).trans (gm_pull f π₁ z _ (l₁ t hz) _)))))⟩
  have indep : ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t t' : M₀.ι × L.ι × L.ι), f z ∈ W t → f z ∈ W t' →
      gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ =
      gw wF (f ≫ π₂) z t'.1 t'.2.2 * gw w f z t'.2.2 (fun _ => t'.2.1) * (gw wF (f ≫ π₁) z t'.1 t'.2.1)⁻¹ := by
    rintro Z f z ⟨a, b, c⟩ ⟨a', b', c'⟩ h h'
    obtain ⟨ha, hb, hc⟩ := (hW _ _).1 h
    obtain ⟨ha', hb', hc'⟩ := (hW _ _).1 h'
    have e₂ := hF Z (f ≫ π₂) z a a' c c' (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha)
      (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha') hc hc'
    have e₁ := hF Z (f ≫ π₁) z a a' b b' ha ha' hb hb'
    have ew := hw Z f z c c' (fun _ => b) (fun _ => b') hc hc' (mem_pull.2 hb) (mem_pull.2 hb')
    rw [gm_pullChart L π₁ f z b b' hb hb'] at ew
    have hg : gm ((f ≫ π₂) ≫ β) z _ (M₀.g a a') = gm ((f ≫ π₁) ≫ β) z _ (M₀.g a a') := by
      simp only [Category.assoc, hβ]
    dsimp only
    rw [e₂, e₁, ew, hg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j₁, h₁⟩ := exists_chart hL (π₁ x)
      obtain ⟨j₂, h₂⟩ := exists_chart hL (π₂ x)
      obtain ⟨j₀, h₀⟩ := exists_chart hM (β (π₁ x))
      exact Opens.mem_iSup.2 ⟨(j₀, j₁, j₂), (hW _ x).2 ⟨h₀, h₁, h₂⟩⟩) u
    (fun t t' x hx => (hu _ (𝟙 B) x t hx.1).trans ((indep _ (𝟙 B) x t t' hx.1 hx.2).trans (hu _ (𝟙 B) x t' hx.2).symm))
  refine ⟨s, fun Z f z j₀ j₁ j₂ h₀ h₁ h₂ => ?_⟩
  have hz : f z ∈ W (j₀, j₁, j₂) := (hW _ _).2 ⟨h₀, h₁, h₂⟩
  exact (gm_res f z le_top hz s).symm.trans ((congrArg (gm f z _) (hs _)).trans (hu Z f z _ hz))

theorem exists_unit : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  intro A _ B' _ hB X Y L M₀ β wF π₁ π₂ w hL hM hwF hw hβ
  obtain ⟨s, hs⟩ := exists_glued L M₀ β wF π₁ π₂ w hL hM ((isGen_iff wF).1 hwF) ((isGen_iff w).1 hw) hβ
  have hbij := GlobalTheory.globalFns_holds _ B' hB
  let e := RingEquiv.ofBijective B'.hom.appTop.hom hbij
  let a : Γ(Sp A, ⊤)ˣ := Units.map e.symm.toMonoidHom s
  have ha : Units.map B'.hom.appTop.hom.toMonoidHom a = s := by
    ext
    exact e.apply_symm_apply _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a, ?_⟩
  intro p hp zz J J₀ hJ hJ₀
  have hua : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a) = a := by
    ext
    simp [unitOn]
  have k₁ := gm_pull p B'.hom zz ⊤ trivial a
  rw [hp] at k₁
  have key : gm p zz ⊤ s = gm (𝟙 _) zz ⊤ a := by
    rw [← ha]
    exact k₁
  have hs' := hs (Sp A) p zz (J₀ (p ≫ π₁ ≫ β)) (J (p ≫ π₁)) (J (p ≫ π₂)) (hJ₀ _) (hJ _) (hJ _)
  rw [hua, ← key, show p ≫ π₂ ≫ β = p ≫ π₁ ≫ β by rw [hβ], hs']
  exact (inv_mul_cancel_right _ _).symm

end GlobalTheory.PullAutConst
