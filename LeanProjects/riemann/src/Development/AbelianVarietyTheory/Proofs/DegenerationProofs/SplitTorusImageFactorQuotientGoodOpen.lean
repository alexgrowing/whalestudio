import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioOfWeightSumsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorusImage

theorem appLE_res {Z Y : Scheme.{0}} (g : Z ⟶ Y) {U V : Y.Opens} (hV : V ≤ U) (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g ⁻¹ᵁ U)
    (f : Γ(Y, U)) : (g.appLE V ⊤ h).hom ((Y.presheaf.map (homOfLE hV).op).hom f) = (g.appLE U ⊤ h').hom f := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appTop_appLE {Z' Z Y : Scheme.{0}} (π : Z' ⟶ Z) (g : Z ⟶ Y) (g' : Z' ⟶ Y) (e : π ≫ g = g') {U : Y.Opens}
    (h : ⊤ ≤ g ⁻¹ᵁ U) (h' : ⊤ ≤ g' ⁻¹ᵁ U) (f : Γ(Y, U)) :
    π.appTop.hom ((g.appLE U ⊤ h).hom f) = (g'.appLE U ⊤ h').hom f := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun q => q.hom f) (Scheme.Hom.appLE_comp_appLE π g U ⊤ ⊤ h le_top)

theorem ext_affineOpen {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ g ⁻¹ᵁ U) (h' : ⊤ ≤ g' ⁻¹ᵁ U) (e : g.appLE U ⊤ h = g'.appLE U ⊤ h') : g = g' := by
  have : IsAffine U.toScheme := hU
  have h1 : g.resLE U ⊤ h = g'.resLE U ⊤ h' := by
    apply ext_of_isAffine
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, e]
  have h2 := congrArg (· ≫ U.ι) h1
  simp only [Scheme.Hom.resLE_comp_ι] at h2
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  exact (cancel_epi _).1 h2

theorem exists_finset_ext {S : Scheme.{0}} [IsAffine S] (G : Over S) [LocallyOfFiniteType G.hom] {U : G.left.Opens}
    (hU : IsAffineOpen U) : ∃ s : Finset Γ(G.left, U), ∀ (Z : Over S) (g g' : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ U)
      (h' : ⊤ ≤ g'.left ⁻¹ᵁ U), (∀ f ∈ s, (g.left.appLE U ⊤ h).hom f = (g'.left.appLE U ⊤ h').hom f) → g = g' := by
  have hft : (G.hom.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType G.hom inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let _ := (G.hom.appLE ⊤ U le_top).hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType Γ(S, ⊤) Γ(G.left, U) from hft).out
  refine ⟨s, fun Z g g' h h' e => Over.OverMorphism.ext (ext_affineOpen _ _ hU h h' ?_)⟩
  ext f
  have hf : f ∈ Algebra.adjoin Γ(S, ⊤) (s : Set Γ(G.left, U)) := hs ▸ trivial
  have key : ∀ (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ U) (c : Γ(S, ⊤)),
      (g.left.appLE U ⊤ h).hom ((G.hom.appLE ⊤ U le_top).hom c) = (Z.hom.appLE ⊤ ⊤ le_top).hom c := by
    intro g h c
    have aux : ∀ q : Z.left ⟶ S, g.left ≫ G.hom = q → ∀ hq, (g.left.appLE U ⊤ h).hom
        ((G.hom.appLE ⊤ U le_top).hom c) = (q.appLE ⊤ ⊤ hq).hom c := by
      rintro _ rfl hq
      exact congrArg (fun q => q.hom c) (Scheme.Hom.appLE_comp_appLE g.left G.hom ⊤ U ⊤ le_top h)
    exact aux _ (Over.w g) _
  induction hf using Algebra.adjoin_induction with
  | mem x hx => exact e x hx
  | algebraMap c => exact (key g h c).trans (key g' h' c).symm
  | add x y _ _ a b => rw [map_add, map_add, a, b]
  | mul x y _ _ a b => rw [map_mul, map_mul, a, b]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem appTop_charUnit {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = SplitTorus.val t χ := by
  rw [SplitTorus.charUnit_val, SplitTorus.val_eq]

theorem wt_res {U V : G.left.Opens} (hV : V ≤ U) {u : Γ(G.left, U)} {χ : X} (h : Wt i U u χ) :
    Wt i V ((G.left.presheaf.map (homOfLE hV).op).hom u) χ := by
  intro Z t g h₁ h₂
  rw [appLE_res _ hV h₁ (h₁.trans fun _ hx => hV hx), appLE_res _ hV h₂ (h₂.trans fun _ hx => hV hx)]
  exact h Z t g _ _

theorem wt_one (U : G.left.Opens) : Wt i U 1 0 := by
  intro Z t g h₁ h₂
  rw [appTop_charUnit, SplitTorus.val_zero, map_one, map_one, _root_.mul_one]

theorem wt_mul {U : G.left.Opens} {u v : Γ(G.left, U)} {χ ψ : X} (h : Wt i U u χ) (h' : Wt i U v ψ) :
    Wt i U (u * v) (χ + ψ) := by
  intro Z t g h₁ h₂
  rw [map_mul, map_mul, h Z t g h₁ h₂, h' Z t g h₁ h₂, appTop_charUnit, appTop_charUnit, appTop_charUnit,
    SplitTorus.val_add]
  ring

theorem wt_inv {U : G.left.Opens} {u v : Γ(G.left, U)} (e : u * v = 1) {χ : X} (h : Wt i U u χ) :
    Wt i U v (-χ) := by
  intro Z t g h₁ h₂
  have a := h Z t g h₁ h₂
  have b := congrArg (((t ≫ i) * g).left.appLE U ⊤ h₁).hom e
  have c := congrArg (g.left.appLE U ⊤ h₂).hom e
  have d : SplitTorus.val t χ * SplitTorus.val t (-χ) = 1 := by
    rw [← SplitTorus.val_add, add_neg_cancel, SplitTorus.val_zero]
  rw [map_mul, map_one] at b c
  rw [appTop_charUnit] at a ⊢
  rw [a] at b
  linear_combination (SplitTorus.val t (-χ) * (g.left.appLE U ⊤ h₂).hom v) * b
    - (((t ≫ i) * g).left.appLE U ⊤ h₁).hom v * (SplitTorus.val t χ * SplitTorus.val t (-χ)) * c
    - (((t ≫ i) * g).left.appLE U ⊤ h₁).hom v * d

variable (i) in

def weights [IrreducibleSpace G.left] : AddSubgroup X where
  carrier := {χ | ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ}
  zero_mem' := ⟨⊤, 1, Set.univ_nonempty, isUnit_one, wt_one _⟩
  add_mem' := by
    rintro χ ψ ⟨U, u, hU, hu, h⟩ ⟨V, v, hV, hv, h'⟩
    exact ⟨U ⊓ V, _, nonempty_preirreducible_inter U.2 V.2 hU hV,
      (hu.map _).mul (hv.map _), wt_mul (wt_res inf_le_left h) (wt_res inf_le_right h')⟩
  neg_mem' := by
    rintro χ ⟨U, u, hU, hu, h⟩
    obtain ⟨v, e⟩ := hu.exists_right_inv
    exact ⟨U, v, hU, IsUnit.of_mul_eq_one_right u e, wt_inv e h⟩

theorem wt_desc {X' : Type} [AddCommGroup X'] (φ : X' →+ X) (hφ : Function.Injective φ) (i' : splitTorus S X' ⟶ G)
    (e : Diag.diagMap S φ ≫ i' = i) {U : G.left.Opens} {u : Γ(G.left, U)} {χ : X'} (h : Wt i U u (φ χ)) :
    Wt i' U u χ := by
  intro Z t g h₁ h₂
  have := Diag.flat_diagMap S hφ
  have := Diag.surjective_diagMap S hφ
  let Z' : Over S := Over.mk (pullback.fst t.left (Diag.diagMap S φ).left ≫ Z.hom)
  let π : Z' ⟶ Z := Over.homMk (pullback.fst t.left (Diag.diagMap S φ).left) rfl
  let t' : Z' ⟶ splitTorus S X := Over.homMk (pullback.snd t.left (Diag.diagMap S φ).left) (by
    show _ = pullback.fst _ _ ≫ _
    rw [← Over.w (Diag.diagMap S φ), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w])
  have hc : π ≫ t = t' ≫ Diag.diagMap S φ := Over.OverMorphism.ext pullback.condition
  have : Epi π.left := Flat.epi_of_flat_of_surjective (pullback.fst t.left (Diag.diagMap S φ).left)
  apply FunDescent.appTop_injective π.left
  have e1 : π.left ≫ ((t ≫ i') * g).left = ((t' ≫ i) * (π ≫ g)).left := by
    rw [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, hc, Category.assoc, e]
  have k1 : ⊤ ≤ ((t' ≫ i) * (π ≫ g)).left ⁻¹ᵁ U := by
    rw [← e1]; exact fun x _ => h₁ (trivial : π.left x ∈ (⊤ : Z.left.Opens))
  have k2 : ⊤ ≤ (π ≫ g).left ⁻¹ᵁ U := fun x _ => h₂ (trivial : π.left x ∈ (⊤ : Z.left.Opens))
  rw [map_mul, appTop_appLE _ _ _ e1 h₁ k1, appTop_appLE _ _ (π ≫ g).left rfl h₂ k2, h Z' t' (π ≫ g) k1 k2,
    appTop_charUnit, appTop_charUnit, ← SplitTorus.val_comp, hc, SplitTorus.val_comp t', SplitTorus.val_eq (Diag.diagMap S φ),
    Diag.diagMap_chi, SplitTorus.val_eq]

theorem eq_one_of_open [Flat G.hom] [GeometricallyIrreducible G.hom] (U : G.left.Opens)
    (hU : ∀ s : S, ∃ y ∈ U, G.hom y = s) {Z : Over S} (x : Z ⟶ G)
    (h : ∀ (Y : Over S) (π : Y ⟶ Z) (g : Y ⟶ G), ⊤ ≤ ((π ≫ x) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U → (π ≫ x) * g = g) :
    x = 1 := by
  let a : Z ⊗ G ⟶ G := (fst Z G ≫ x) * snd Z G
  let O : (Z ⊗ G).left.Opens := a.left ⁻¹ᵁ U ⊓ (snd Z G).left ⁻¹ᵁ U
  let Y : Over S := Over.mk (O.ι ≫ (Z ⊗ G).hom)
  let j : Y ⟶ Z ⊗ G := Over.homMk O.ι rfl
  have e1 : ((j ≫ fst Z G) ≫ x) * (j ≫ snd Z G) = j ≫ a := by
    rw [MonObj.comp_mul, Category.assoc]
  have h1 := h Y (j ≫ fst Z G) (j ≫ snd Z G) (by rw [e1]; exact fun y _ => y.2.1) (fun y _ => y.2.2)
  have h2 : (j ≫ fst Z G) ≫ x = (j ≫ fst Z G) ≫ 1 := by
    rw [MonObj.comp_one]; exact mul_eq_right.1 h1
  have hf : Flat (fst Z G).left := inferInstanceAs (Flat (pullback.fst Z.hom G.hom))
  have hg : GeometricallyIrreducible (fst Z G).left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst Z.hom G.hom))
  have : Flat (j ≫ fst Z G).left := inferInstanceAs (Flat (O.ι ≫ (fst Z G).left))
  have m2 : ∀ z : Z.left, ∃ w : (Z ⊗ G).left, (snd Z G).left w ∈ U ∧ (fst Z G).left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hU (Z.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : Z.left, ∃ w : (Z ⊗ G).left, a.left w ∈ U ∧ (fst Z G).left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : Z ⊗ G ⟶ Z ⊗ G := lift (fst Z G) ((fst Z G ≫ x)⁻¹ * snd Z G)
    have b1 : b ≫ a = snd Z G := by
      simp [a, b, MonObj.comp_mul, ← Category.assoc]
    have b2 : b ≫ fst Z G = fst Z G := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  have : Surjective (j ≫ fst Z G).left := ⟨fun z => by
    have hi : IsIrreducible ((fst Z G).left ⁻¹' {z}) := by
      rw [← (fst Z G).left.range_fiberι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ ((fst Z G).left.fiberι z).continuous.continuousOn
    obtain ⟨w, hw, e⟩ := m1 z
    obtain ⟨w', hw', e'⟩ := m2 z
    obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ U).2 ((snd Z G).left ⁻¹ᵁ U).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
    exact ⟨⟨y, k₁, k₂⟩, hy⟩⟩
  have := FlatQuotient.epi_of_flat_surjective (j ≫ fst Z G)
  exact (cancel_epi _).1 h2
end

theorem exists_open (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : SmConn G)
    [IrreducibleSpace G.left] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp k) X ⟶ G) (hi : IsMonHom i) :
    ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧ ∀ (Y : Over (Sp k)) (t : Y ⟶ splitTorus (Sp k) X) (g : Y ⟶ G),
      (∀ χ ∈ weights i, SplitTorus.val t χ = 1) → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U →
      (t ≫ i) * g = g := by
  have := hG.2.1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := ⊤) (x := x) trivial
  obtain ⟨s, hs⟩ := exists_finset_ext G hW
  have one : ∀ f : Γ(G.left, W), ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧
      ∀ (Y : Over (Sp k)) (t : Y ⟶ splitTorus (Sp k) X) (g : Y ⟶ G),
      (∀ χ ∈ weights i, SplitTorus.val t χ = 1) → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U →
      ∀ h₁ h₂, (((t ≫ i) * g).left.appLE W ⊤ h₁).hom f = (g.left.appLE W ⊤ h₂).hom f := by
    intro f
    obtain ⟨U, hU, n, a, b, χ, hne, hw, hb, e⟩ := GlobalTheory.T.exists_ratio_of_weight_sums' k G hG X i hi W f ⟨x, hx⟩
    refine ⟨U, hne, fun Y t g ht k₁ k₂ h₁ h₂ => ?_⟩
    have key : ∀ (c : Γ(G.left, U)) (ψ : X), Wt i U c ψ → (c = 0 ∨ IsUnit c) →
        (((t ≫ i) * g).left.appLE U ⊤ k₁).hom c = (g.left.appLE U ⊤ k₂).hom c := by
      rintro c ψ hc (rfl | hu)
      · rw [map_zero, map_zero]
      · rw [hc Y t g k₁ k₂, appTop_charUnit, ht ψ ⟨U, c, hne, hu, hc⟩, _root_.one_mul]
    have ea : (((t ≫ i) * g).left.appLE U ⊤ k₁).hom (∑ j, a j) = (g.left.appLE U ⊤ k₂).hom (∑ j, a j) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => key _ _ (hw j).1 (hw j).2.2.1
    have eb : (((t ≫ i) * g).left.appLE U ⊤ k₁).hom (∑ j, b j) = (g.left.appLE U ⊤ k₂).hom (∑ j, b j) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => key _ _ (hw j).2.1 (hw j).2.2.2
    rw [← e, map_mul, map_mul, eb, appLE_res _ hU k₁ h₁, appLE_res _ hU k₂ h₂] at ea
    exact (hb.map (g.left.appLE U ⊤ k₂).hom).mul_right_cancel ea
  choose V hV hV' using one
  have fin : ∀ s : Finset Γ(G.left, W), ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧ U ≤ W ∧ ∀ f ∈ s, U ≤ V f := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, ⟨x, hx⟩, le_rfl, by simp⟩
    | insert f s _ ih =>
      obtain ⟨U, h1, h2, h3⟩ := ih
      refine ⟨U ⊓ V f, nonempty_preirreducible_inter U.2 (V f).2 h1 (hV f), inf_le_left.trans h2, fun f' hf' => ?_⟩
      rcases Finset.mem_insert.1 hf' with rfl | hf'
      · exact inf_le_right
      · exact inf_le_left.trans (h3 f' hf')
  obtain ⟨U, h1, h2, h3⟩ := fin s
  refine ⟨U, h1, fun Y t g ht k₁ k₂ => hs Y _ _ (k₁.trans fun _ hy => h2 hy) (k₂.trans fun _ hy => h2 hy) fun f hf => ?_⟩
  exact hV' f Y t g ht (k₁.trans fun _ hy => h3 f hf hy) (k₂.trans fun _ hy => h3 f hf hy) _ _

theorem exists_factor_goodOpen : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module.Free ℤ X') (_ : Module.Finite ℤ X') (i' : splitTorus (Sp k) X' ⟶ G) (ρ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X'), IsMonHom i' ∧ IsMonHom ρ ∧ Surjective ρ.left ∧ ρ ≫ i' = i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i' V) := by
  intro k _ _ G _ hG X _ _ _ i hi
  have := hG.2.1
  have := hG.2.2.2.2
  have : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth G.hom
  have : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.hom
  obtain ⟨U, ⟨y, hy⟩, hU⟩ := exists_open k G hG X i hi
  let φ : weights i →+ X := (weights i).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hfree : Module.Free ℤ (weights i) := inferInstanceAs (Module.Free ℤ (weights i).toIntSubmodule)
  have hfin : Module.Finite ℤ (weights i) := inferInstanceAs (Module.Finite ℤ (weights i).toIntSubmodule)
  let ρ := Diag.diagMap (Sp k) φ
  have : Flat ρ.left := Diag.flat_diagMap _ hφ
  have hsurj : Surjective ρ.left := Diag.surjective_diagMap _ hφ
  have : QuasiCompact (ρ.left ≫ (splitTorus (Sp k) (weights i)).hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ρ.left := .of_comp _ (splitTorus (Sp k) (weights i)).hom
  have hker : IsPullback (pullback.fst ρ η[splitTorus (Sp k) (weights i)]) (toUnit _) ρ η := by
    rw [← toUnit_unique (pullback.snd ρ η[splitTorus (Sp k) (weights i)]) (toUnit _)]
    exact IsPullback.of_hasPullback _ _
  have hkill : pullback.fst ρ η[splitTorus (Sp k) (weights i)] ≫ i = toUnit _ ≫ η[G] := by
    rw [← Hom.one_def]
    refine eq_one_of_open U (fun s => ⟨y, hy, Subsingleton.elim _ _⟩) _ fun Y π g h₁ h₂ => ?_
    rw [← Category.assoc] at h₁ ⊢
    refine hU Y _ g (fun χ hχ => ?_) h₁ h₂
    have e : (π ≫ pullback.fst ρ η[splitTorus (Sp k) (weights i)]) ≫ ρ = 1 := by
      rw [Category.assoc, hker.w, ← Hom.one_def, MonObj.comp_one]
    have e' := SplitTorus.val_one (T := Y) (⟨χ, hχ⟩ : weights i)
    rw [← e, SplitTorus.val_comp, SplitTorus.val_eq ρ, Diag.diagMap_chi, ← SplitTorus.val_eq] at e'
    exact e'
  obtain ⟨i', hi', e⟩ := FlatQuotient.exists_desc ρ _ i hker hkill
  refine ⟨weights i, inferInstance, hfree, hfin, i', ρ, hi', inferInstance, hsurj, e,
    GlobalTheory.T.exists_torusStableGoodOpen_of_weightUnits k G hG (weights i) i' hi' fun χ => ?_⟩
  obtain ⟨V, u, hV, hu, h⟩ := χ.2
  exact ⟨V, u, hV, hu, wt_desc φ hφ i' e h⟩

end GlobalTheory.TorusImage
