import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory
namespace NormGlue

theorem appLE_eq_appIso {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens)
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) (h' : f ''ᵁ V ≤ W) (ψ : Γ(X, W)) :
    (f.appLE W V h).hom ψ = (f.appIso V).hom.hom (resG X h' ψ) := by
  rw [Scheme.Hom.appIso_hom']
  change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom ψ
  rw [Scheme.Hom.map_appLE]

theorem image_le {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] {W : X.Opens}
    {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W) : f ''ᵁ V ≤ W := by
  rintro _ ⟨x, hx, rfl⟩
  exact h hx

theorem appLE_injective {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) (hV : (V : Set Y).Nonempty) :
    Function.Injective (f.appLE W V h).hom := by
  intro a b hab
  rw [appLE_eq_appIso f W V h (image_le f h), appLE_eq_appIso f W V h (image_le f h)] at hab
  have h1 := (f.appIso V).commRingCatIsoToRingEquiv.injective hab
  obtain ⟨x, hx⟩ := hV
  haveI : Nonempty (f ''ᵁ V) := ⟨⟨f x, x, hx, rfl⟩⟩
  exact map_injective_of_isIntegral X (homOfLE (image_le f h)) h1

theorem valF_comp_appIso {F : Type} [Field F] {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (V : Y.Opens) (u : Γ(Y, V)) (y₀ : Sp F ⟶ Y) :
    valF (y₀ ≫ f) (f ''ᵁ V) ((f.appIso V).inv.hom u) = valF y₀ V u := by
  have e : (y₀ ≫ f) ⁻¹ᵁ (f ''ᵁ V) = y₀ ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
  unfold valF
  by_cases h : ⊤ ≤ y₀ ⁻¹ᵁ V
  · rw [dif_pos h, dif_pos (e ▸ h)]
    congr 1
    rw [← Scheme.Hom.appLE_comp_appLE y₀ f (f ''ᵁ V) V ⊤ (f.preimage_image_eq V).ge h,
      ← Scheme.Hom.appIso_hom']
    change (y₀.appLE V ⊤ h).hom (((f.appIso V).inv ≫ (f.appIso V).hom).hom u) = _
    rw [Iso.inv_hom_id]
    rfl
  · rw [dif_neg h, dif_neg (e ▸ h)]

theorem val_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ W) (ψ : Γ(X, W)ˣ) :
    (Semi.res h (pullU f W ψ)).val = (f.appLE W V h).hom ψ.val := rfl

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ ξ : Y, ∀ O : Y.Opens, (O : Set Y).Nonempty → ξ ∈ O :=
  ⟨genericPoint Y, fun O hO => ((genericPoint_spec Y).mem_open_set_iff O.isOpen).2 (by simpa using hO)⟩

theorem preimage_nonempty {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) [IsOpenImmersion f] (y : Y)
    {U : X.Opens} (hU : (U : Set X).Nonempty) : ((f ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, ⟨y', rfl⟩, hx⟩ := nonempty_preirreducible_inter f.isOpenEmbedding.isOpen_range U.isOpen
    ⟨f y, y, rfl⟩ hU
  exact ⟨y', hx⟩

theorem unit_eq_of_gm {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) [IsOpenImmersion f] (ξ : Y)
    (hξ : ∀ O : Y.Opens, (O : Set Y).Nonempty → ξ ∈ O) {U : X.Opens} {u u' : Γ(X, U)ˣ}
    (h : f ξ ∈ U → gm f ξ U u = gm f ξ U u') : u = u' := by
  by_cases hU : (U : Set X).Nonempty
  · haveI : Nonempty Y := ⟨ξ⟩
    haveI : IsIntegral Y := isIntegral_of_isOpenImmersion f
    have hne := preimage_nonempty f ξ hU
    have hm : f ξ ∈ U := hξ _ hne
    have e := congrArg Units.val (h hm)
    rw [gm_val f ξ U hm, gm_val f ξ U hm] at e
    have e' := germ_injective_of_isIntegral Y (U := f ⁻¹ᵁ U) ξ hm e
    apply Units.ext
    apply appLE_injective f U (f ⁻¹ᵁ U) le_rfl hne
    rw [Scheme.Hom.appLE_eq_app]
    exact e'
  · exact unit_ext fun x hx => (hU ⟨x, hx⟩).elim

theorem mem_of_range {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : Set X}
    (h : Set.range x ⊆ U) (z : Sp F) : x z ∈ U := h ⟨z, rfl⟩

theorem range_sub {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : Set X} (z : Sp F)
    (h : x z ∈ U) : Set.range x ⊆ U := by
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim y z]

theorem valF_eq_of_gm {F : Type} [Field F] {X X' : Scheme.{0}} {x : Sp F ⟶ X} {x' : Sp F ⟶ X'}
    {U : X.Opens} {U' : X'.Opens} (z : Sp F) (h : x z ∈ U) (h' : x' z ∈ U') {u : Γ(X, U)ˣ} {u' : Γ(X', U')ˣ}
    (e : gm x z U u = gm x' z U' u') : valF x U u.val = valF x' U' u'.val :=
  (toStk z).injective (by rw [toStk_valF x U z h, toStk_valF x' U' z h', e])

theorem range_sub_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : Set X} (hU : IsOpen U) (h : b (IsLocalRing.closedPoint R) ∈ U) : Set.range b ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map b.continuous).mem_open hU h

theorem IntAt_mem {X Y : Scheme.{0}} {a : X ⟶ Y} {W : Y.Opens} {p : ℕ} [Fact p.Prime]
    {x : Sp (PadicAlgCl p) ⟶ X} (h : IntAt a W x) (z : Sp (PadicAlgCl p)) : a (x z) ∈ W := by
  obtain ⟨b, hb, hc⟩ := h
  have : (gPt p ≫ b) z ∈ W := range_sub_of_closedPoint b W.isOpen hc ⟨gPt p z, rfl⟩
  rw [hb] at this
  exact this

theorem exists_ext (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π]
    [LocallyOfFiniteType π] (hX : Geo.Tor.IsNormalScheme X) {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) (hne : (W : Set X).Nonempty → (V : Set Y).Nonempty)
    (u : Γ(Y, V)ˣ)
    (hu : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ Y), IntAt f W x → Set.range x ⊆ V →
      ‖valF x V u.val‖ = 1) :
    ∃ ψ : Γ(X, W)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ f) z W ψ = gm r z V u := by
  by_cases hW : (W : Set X).Nonempty
  · obtain ⟨y, hy⟩ := hne hW
    obtain ⟨ψ, hψ, e⟩ := (GlobalTheory.regular_of_bounded_at_padicAlgCl_points.2 X π hX (f ''ᵁ V) W (image_le _ h)
      ((f.appIso V).inv.hom u.val) ⟨f y, y, hy, rfl⟩).2 (u.isUnit.map _) (by
        intro p _ b hb hr
        have hr' : Set.range (gPt p ≫ b) ⊆ Set.range f := by
          intro t ht
          obtain ⟨s, -, rfl⟩ := hr ht
          exact ⟨s, rfl⟩
        have fac := IsOpenImmersion.lift_fac f (gPt p ≫ b) hr'
        set x := IsOpenImmersion.lift f (gPt p ≫ b) hr'
        have hx : Set.range x ⊆ V := by
          rintro _ ⟨t, rfl⟩
          have : (x ≫ f) t ∈ f ''ᵁ V := by rw [fac]; exact hr ⟨t, rfl⟩
          obtain ⟨s, hs, e⟩ := this
          have : s = x t := f.isOpenEmbedding.injective e
          exact this ▸ hs
        have := hu p x ⟨b, fac.symm, hb⟩ hx
        rw [← valF_comp_appIso f V u.val x, fac] at this
        exact this)
    have e' : Semi.res h (pullU f W hψ.unit) = u := by
      apply Units.ext
      rw [val_res_pullU, appLE_eq_appIso f W V h (image_le f h), IsUnit.unit_spec, e]
      exact Iso.inv_hom_id_apply _ _
    refine ⟨hψ.unit, fun Z r z hz => ?_⟩
    rw [← e', gm_res r z h hz, gm_pull r f z W (h hz)]
  · exact ⟨1, fun Z r z hz => (hW ⟨_, h hz⟩).elim⟩

theorem exists_coord (X A₀ : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hX : Geo.Tor.IsNormalScheme X) (a : A₀ ⟶ X) [IsOpenImmersion a] (L : LB A₀) (ν : Nrm L) (hν : IsNrm L ν)
    (W : X.Opens) (W₀ : A₀.Opens) (gn : LB.Gen (L.pull W₀.ι)) (hW₀ : (W₀ : Set A₀).Nonempty) (hgen : gn.IsGen)
    (hn : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ a) W x → NormOne ν gn x) :
    ∃ s : ∀ j, Γ(A₀, L.U j ⊓ a ⁻¹ᵁ W)ˣ,
      (∀ (y : A₀) (j j' : L.ι), y ∈ L.U j → y ∈ L.U j' → a y ∈ W →
        gm (𝟙 A₀) y _ (s j) = gm (𝟙 A₀) y _ (L.g j j') * gm (𝟙 A₀) y _ (s j')) ∧
      ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ A₀) (j : L.ι), IntAt a W x → Set.range x ⊆ L.U j →
        Set.range x ⊆ W₀ → ‖valF x _ (s j).val‖ * ν p x j = 1 := by
  obtain ⟨y₀, hy₀⟩ := hW₀
  haveI : Nonempty A₀ := ⟨y₀⟩
  haveI : IsIntegral A₀ := isIntegral_of_isOpenImmersion a
  haveI : Nonempty W₀.toScheme := ⟨⟨y₀, hy₀⟩⟩
  haveI : IsIntegral W₀.toScheme := isIntegral_of_isOpenImmersion W₀.ι
  obtain ⟨ξ, hξ⟩ := exists_generic W₀.toScheme
  have key : ∀ j, ∃ s : Γ(A₀, L.U j ⊓ a ⁻¹ᵁ W)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ W₀.toScheme) (z : Z),
      W₀.ι (r z) ∈ L.U j → a (W₀.ι (r z)) ∈ W →
      gm (r ≫ W₀.ι) z _ s = gm r z ((L.pull W₀.ι).U (fun _ => j)) (gn.s (fun _ => j)) := by
    intro j
    obtain ⟨ψ, hψ⟩ := exists_ext X π hX (W₀.ι ≫ a) (a ''ᵁ (L.U j ⊓ a ⁻¹ᵁ W))
      ((L.pull W₀.ι).U (fun _ => j) ⊓ (W₀.ι ≫ a) ⁻¹ᵁ W)
      (fun y hy => ⟨W₀.ι y, ⟨mem_pull.1 hy.1, hy.2⟩, rfl⟩)
      (by
        rintro ⟨_, y, hy, rfl⟩
        obtain ⟨t, ht⟩ := preimage_nonempty W₀.ι ξ (U := L.U j ⊓ a ⁻¹ᵁ W) ⟨y, hy⟩
        exact ⟨t, mem_pull.2 ht.1, ht.2⟩)
      (Semi.res inf_le_left (gn.s (fun _ => j))) (by
        rintro p _ x ⟨b, hb, c, hc, hcb⟩ hx
        let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
        have hr : Set.range b ⊆ Set.range a :=
          range_sub_of_closedPoint b a.isOpenEmbedding.isOpen_range ⟨c, hcb⟩
        have fac := IsOpenImmersion.lift_fac a b hr
        set b' := IsOpenImmersion.lift a b hr
        have hb' : gPt p ≫ b' = x ≫ W₀.ι := by
          rw [← cancel_mono a, Category.assoc, fac, hb, Category.assoc]
        have hc' : b' (cPt p) = c := a.isOpenEmbedding.injective
          ((congrArg (fun q : Sp (OO p) ⟶ X => q (cPt p)) fac).trans hcb.symm)
        have h1 := hν.int p b' j (hc' ▸ hc.1)
        have h2 := hn p x ⟨b, hb, hcb ▸ hc.2⟩ (fun _ => j) (fun t ht => (hx ht).1)
        rw [Fintype.prod_unique, zpow_one, ← hb', h1, _root_.mul_one] at h2
        rw [← h2]
        exact congrArg _ (valF_eq_of_gm z (mem_of_range hx z) (mem_of_range hx z).1
          (gm_res x z _ (mem_of_range hx z) _)))
    refine ⟨Semi.res (a.preimage_image_eq _).ge (pullU a _ ψ), fun Z r z h₁ h₂ => ?_⟩
    have hm : (r ≫ W₀.ι) z ∈ L.U j ⊓ a ⁻¹ᵁ W := ⟨h₁, h₂⟩
    have hm' : r z ∈ (L.pull W₀.ι).U (fun _ => j) ⊓ (W₀.ι ≫ a) ⁻¹ᵁ W := ⟨mem_pull.2 h₁, h₂⟩
    rw [gm_res _ z _ hm, gm_pull (r ≫ W₀.ι) a z (a ''ᵁ (L.U j ⊓ a ⁻¹ᵁ W)) ⟨_, hm, rfl⟩, Category.assoc, hψ Z r z hm', gm_res r z _ hm']
  choose s hs using key
  refine ⟨s, fun y j j' hj hj' hy => ?_, fun p _ x j hx hj h₀ => ?_⟩
  · have l₁ : L.U j ⊓ L.U j' ⊓ a ⁻¹ᵁ W ≤ L.U j ⊓ a ⁻¹ᵁ W := inf_le_inf_right _ inf_le_left
    have l₂ : L.U j ⊓ L.U j' ⊓ a ⁻¹ᵁ W ≤ L.U j' ⊓ a ⁻¹ᵁ W := inf_le_inf_right _ inf_le_right
    have e : Semi.res l₁ (s j) = Semi.res inf_le_left (L.g j j') * Semi.res l₂ (s j') := by
      refine unit_eq_of_gm W₀.ι ξ hξ fun hm => ?_
      rw [map_mul, gm_res _ ξ _ hm, gm_res _ ξ _ hm, gm_res _ ξ _ hm]
      have e₁ := hs j _ (𝟙 _) ξ hm.1.1 hm.2
      have e₂ := hs j' _ (𝟙 _) ξ hm.1.2 hm.2
      have e₃ := gen_trans hgen (𝟙 _) ξ (j := fun _ => j) (j' := fun _ => j') (mem_pull.2 hm.1.1) (mem_pull.2 hm.1.2)
      rw [trF, Fintype.prod_unique, zpow_one] at e₃
      rw [Category.id_comp] at e₁ e₂ e₃
      rw [e₁, e₂]
      exact e₃
    have hm : (𝟙 A₀ : A₀ ⟶ A₀) y ∈ L.U j ⊓ L.U j' ⊓ a ⁻¹ᵁ W := ⟨⟨hj, hj'⟩, hy⟩
    have := congrArg (gm (𝟙 A₀) y _) e
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_res _ y _ hm] at this
  · let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
    have hr : Set.range x ⊆ Set.range W₀.ι := by rw [Scheme.Opens.range_ι]; exact h₀
    have fac := IsOpenImmersion.lift_fac W₀.ι x hr
    generalize IsOpenImmersion.lift W₀.ι x hr = x' at fac
    subst fac
    have h₁ : W₀.ι (x' z) ∈ L.U j := mem_of_range hj z
    have h₂ : a (W₀.ι (x' z)) ∈ W := IntAt_mem hx z
    obtain ⟨b, hb, hc⟩ := hx
    have h := hn p x' ⟨b, hb.trans (Category.assoc _ _ _), hc⟩ (fun _ => j) (range_sub z (mem_pull.2 h₁))
    rw [Fintype.prod_unique, zpow_one] at h
    rw [← h, valF_eq_of_gm z (show (x' ≫ W₀.ι) z ∈ L.U j ⊓ a ⁻¹ᵁ W from ⟨h₁, h₂⟩) (mem_pull.2 h₁) (hs j _ x' z h₁ h₂)]

end NormGlue
open NormGlue in

theorem exists_lineBundle_of_normOne_generators : ∀ (X A₀ : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π], Geo.Tor.IsNormalScheme X → ∀ (a : A₀ ⟶ X) [IsOpenImmersion a] (L : LB A₀), L.IsLB → ∀ ν : Nrm L, IsNrm L ν → (∀ w : X, IsClosed ({w} : Set X) → ∃ (W : X.Opens) (W₀ : A₀.Opens) (gen₀ : LB.Gen (L.pull W₀.ι)), w ∈ W ∧ (W₀ : Set A₀).Nonempty ∧ gen₀.IsGen ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ a) W x → NormOne ν gen₀ x) → ∃ (M : LB X) (w : LB.Iso (M.pull a) L) (D : M.ι → A₀.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set A₀).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ A₀) (i : M.ι) (j : L.ι), IntAt a (M.U i) x → Set.range x ⊆ L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1 := by
  intro X A₀ _ π _ _ hX a _ L hL ν hν H
  obtain ⟨-, -, hJ, hcl, -⟩ := GlobalTheory.jacobson_closedPoints_tools_int X π
  choose W W₀ gn hW hW₀ hgen hn using fun i : {w : X // IsClosed ({w} : Set X)} => H i.1 i.2
  choose s hs hsn using fun i => exists_coord X A₀ π hX a L ν hν (W i) (W₀ i) (gn i) (hW₀ i) (hgen i) (hn i)
  obtain ⟨w₀, hw₀, -⟩ := hcl (genericPoint X) PEmpty (fun k => k.elim) ⊤ trivial
  haveI : Nonempty A₀ := ⟨(hW₀ ⟨w₀, hw₀⟩).some⟩
  haveI : IsIntegral A₀ := isIntegral_of_isOpenImmersion a
  obtain ⟨ξ, hξ⟩ := exists_generic A₀
  obtain ⟨j₀, hj₀⟩ := exists_chart hL ξ
  have hξW : ∀ i, a ξ ∈ W i := fun i => hξ _ (preimage_nonempty a ξ ⟨_, hW i⟩)
  have hξ₀ : ∀ i, ξ ∈ W₀ i := fun i => hξ _ (hW₀ i)
  have key : ∀ i i', ∃ g : Γ(X, W i ⊓ W i')ˣ,
      gm a ξ _ g = gm (𝟙 A₀) ξ _ (s i' j₀) * (gm (𝟙 A₀) ξ _ (s i j₀))⁻¹ := by
    intro i i'
    have hm : (𝟙 A₀ : A₀ ⟶ A₀) ξ ∈ (L.U j₀ ⊓ a ⁻¹ᵁ W i) ⊓ (L.U j₀ ⊓ a ⁻¹ᵁ W i') ⊓ (W₀ i ⊓ W₀ i') :=
      ⟨⟨⟨hj₀, hξW i⟩, hj₀, hξW i'⟩, hξ₀ i, hξ₀ i'⟩
    obtain ⟨g, hg⟩ := exists_ext X π hX a (W i ⊓ W i')
      ((L.U j₀ ⊓ a ⁻¹ᵁ W i) ⊓ (L.U j₀ ⊓ a ⁻¹ᵁ W i') ⊓ (W₀ i ⊓ W₀ i')) (fun t ht => ⟨ht.1.1.2, ht.1.2.2⟩)
      (fun _ => ⟨ξ, hm⟩)
      (Semi.res (inf_le_left.trans inf_le_right) (s i' j₀) * (Semi.res (inf_le_left.trans inf_le_left) (s i j₀))⁻¹)
      (by
        rintro p _ x ⟨b, hb, hc⟩ hx
        let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
        have hz := mem_of_range hx z
        have h₁ := hsn i p x j₀ ⟨b, hb, hc.1⟩ (range_sub z hz.1.1.1) (range_sub z hz.2.1)
        have h₂ := hsn i' p x j₀ ⟨b, hb, hc.2⟩ (range_sub z hz.1.1.1) (range_sub z hz.2.2)
        have e : valF x _ (Semi.res (inf_le_left.trans inf_le_right :
              (L.U j₀ ⊓ a ⁻¹ᵁ W i) ⊓ (L.U j₀ ⊓ a ⁻¹ᵁ W i') ⊓ (W₀ i ⊓ W₀ i') ≤ _) (s i' j₀) *
              (Semi.res (inf_le_left.trans inf_le_left) (s i j₀))⁻¹).val * valF x _ (s i j₀).val =
            valF x _ (s i' j₀).val := by
          apply (toStk z).injective
          rw [map_mul, toStk_valF x _ z hz, toStk_valF x _ z hz.1.1, toStk_valF x _ z hz.1.2, map_mul, map_inv,
            gm_res x z _ hz, gm_res x z _ hz, ← Units.val_mul, inv_mul_cancel_right]
        rw [← e, norm_mul, _root_.mul_assoc, h₁, _root_.mul_one] at h₂
        exact h₂)
    refine ⟨g, ?_⟩
    have := hg _ (𝟙 _) ξ hm
    rwa [Category.id_comp, map_mul, map_inv, gm_res _ ξ _ hm, gm_res _ ξ _ hm] at this
  choose g hg using key
  let M : LB X := ⟨_, W, g⟩
  have le : ∀ (j : L.ι) (I : PUnit → M.ι), L.U j ⊓ (M.pull a).U I ≤ L.U j ⊓ a ⁻¹ᵁ W (I PUnit.unit) :=
    fun j I t ht => ⟨ht.1, (mem_pull (L := M)).1 ht.2⟩
  refine ⟨M, ⟨fun q => Semi.res (le q.1 q.2) (s (q.2 PUnit.unit) q.1)⟩, W₀, ⟨?_, fun i => ?_, fun i j k => ?_⟩,
    ?_, hW₀, ?_⟩
  · exact hJ _ _ fun x hx => ⟨fun _ => trivial, fun _ => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hW _⟩⟩
  · refine unit_eq_of_gm a ξ hξ fun hm => ?_
    rw [gm_res a ξ _ hm, map_one]
    exact (hg i i).trans (mul_inv_cancel _)
  · refine unit_eq_of_gm a ξ hξ fun hm => ?_
    rw [map_mul, gm_res a ξ _ hm, gm_res a ξ _ hm, gm_res a ξ _ hm]
    refine (congrArg₂ (· * ·) (hg i j) (hg j k)).trans (Eq.trans ?_ (hg i k).symm)
    rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  · rintro ⟨j, I⟩ ⟨j', I'⟩
    refine unit_eq_of_gm (𝟙 A₀) ξ hξ fun hm => ?_
    refine ((gm_res _ ξ _ hm _).trans (gm_res _ ξ _ hm.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_div (M.pull a) L (𝟙 A₀) ξ (j, I) (j', I') hm)
        ((gm_res _ ξ _ hm _).trans (gm_res _ ξ _ hm.2 _)))).symm)
    have e := gm_pull_g M a (𝟙 A₀) ξ I I' hm.1.2 hm.2.2
    rw [Category.id_comp] at e
    have e' := e.trans (hg (I PUnit.unit) (I' PUnit.unit))
    have c := gm_cocycle hL (𝟙 A₀) ξ hm.1.1 hm.2.1 hj₀
    have e₁ := hs (I PUnit.unit) ξ j j₀ hm.1.1 hj₀ (hξW _)
    have e₂ := hs (I' PUnit.unit) ξ j' j₀ hm.2.1 hj₀ (hξW _)
    refine e₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => _ * t⁻¹) e') e₂).symm)
    have alg : ∀ {G : Type} [CommGroup G] (u v t c d : G), u * v = t → t * c = u * (d * c⁻¹)⁻¹ * (v * d) := by
      intro G _ u v t c d h
      rw [← h, mul_inv, inv_inv]
      simp [mul_comm, mul_left_comm, _root_.mul_assoc]
    exact alg _ _ _ _ _ c
  · intro p _ x i j hx hj hD
    let z : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
    have h₁ : x z ∈ L.U j ⊓ (M.pull a).U (fun _ => i) :=
      ⟨mem_of_range hj z, (mem_pull (L := M)).2 (IntAt_mem hx z)⟩
    rw [← hsn i p x j hx hj hD]
    exact congrArg (fun t => ‖t‖ * ν p x j) (valF_eq_of_gm z h₁ (le _ _ h₁) (gm_res x z _ h₁ _))

end GlobalTheory
