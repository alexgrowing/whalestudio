import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsNilpotentOfIsNilDP
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.TagIso
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsDPMorphismId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

abbrev chartOpen (s : X ⟶ Sp R) : Chart s → X.Opens := fun U ↦ U.1.1

theorem exists_lev {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ n, 1 ≤ n ∧ IsLev δ n := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, by omega, Ideal.span_eq_bot.2 ?_⟩
  rintro _ ⟨l, hl, hN, rfl⟩
  exact h l hl (by omega)

variable {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem acyc_NT (T : Tag (dp0 R) s (chartOpen s)) :
    Acyc R (CostructuredArrow (NT κ (chartOpen s)).ι T) := by
  obtain ⟨n, hn, hT⟩ := exists_lev T.T.nil
  obtain ⟨a₀⟩ := exists_lift T.k T.T T.le
  let D := CostructuredArrow (NT κ (chartOpen s)).ι T
  let mk : ∀ (S : Thick (dp0 R) s) (_ : InN κ S) (_ : ⊤ ≤ S.x ⁻¹ᵁ T.k.1.1) (_ : S ⟶ T.T), D := fun S hS h c ↦
    CostructuredArrow.mk (Y := (⟨⟨S, T.k, h⟩, hS⟩ : (NT κ (chartOpen s)).FullSubcategory))
      (⟨c, le_rfl⟩ : Tag.Hom (⟨S, T.k, h⟩ : Tag (dp0 R) s (chartOpen s)) T)
  let c : ∀ a : D, a.left.obj.T ⟶ T.T := fun a ↦ Tag.Hom.f a.hom
  have hk : ∀ a : D, chartOpen s a.left.obj.k ≤ chartOpen s T.k := fun a ↦ Tag.Hom.le a.hom
  have hle : ∀ a : D, ⊤ ≤ a.left.obj.T.x ⁻¹ᵁ T.k.1.1 := fun a p hp ↦ hk a (a.left.obj.le hp)
  let u : ∀ {a b : D}, (a ⟶ b) → (a.left.obj.T ⟶ b.left.obj.T) := fun f ↦ Tag.Hom.f f.left.hom
  have hu : ∀ {a b : D} (f : a ⟶ b), u f ≫ c b = c a := fun f ↦
    congrArg Tag.Hom.f (CostructuredArrow.w f)
  have ext : ∀ {a b : D} (f g : a ⟶ b), u f = u g → f = g := fun f g h ↦
    CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Tag.hom_ext h))
  let hom : ∀ (a b : D) (φ : a.left.obj.T ⟶ b.left.obj.T) (_ : chartOpen s a.left.obj.k ≤ chartOpen s b.left.obj.k)
      (_ : φ ≫ c b = c a), a ⟶ b := fun a b φ h e ↦
    CostructuredArrow.homMk (ObjectProperty.homMk (⟨φ, h⟩ : Tag.Hom _ _)) (Tag.hom_ext e)
  choose P i j hP hl hun using fun a : D ↦ exists_coprod T.k a.left.obj.T a.left.property (hle a) n hn
  choose q hq using fun a : D ↦ (hun a T.T hT (c a) a₀).exists
  let d : D := mk _ (bas_inN T.k) (bas_le T.k.1) a₀
  let Q : D → D := fun a ↦ mk (P a) (hP a) ((i a).le_preimage (hle a)) (q a)
  refine acyc_of_coprod d Q (fun a ↦ hom a (Q a) (i a) (hk a) (hq a).1)
    (fun a ↦ hom d (Q a) (j a) le_rfl (hq a).2) fun a b φ ↦ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := hun a (P b) (hl b) (u φ) (j b)
  have e : ψ ≫ q b = q a := by
    refine (hun a T.T hT (c a) a₀).unique ⟨?_, ?_⟩ (hq a)
    · rw [← Category.assoc, hψ.1]; exact hu φ
    · rw [← Category.assoc, hψ.2]; exact (hq b).2
  refine ⟨hom (Q a) (Q b) ψ le_rfl e, ⟨ext _ _ hψ.1, ext _ _ hψ.2⟩, fun χ hχ ↦ ext _ _ ?_⟩
  exact hψ' (u χ) ⟨congrArg u hχ.1, congrArg u hχ.2⟩

section Final

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}

theorem red_cover (hs : Smooth s) (i : X₀ ⟶ X) : ⨆ k, redOpen (chartOpen s) i k = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, chart_cover hs, Scheme.Hom.preimage_top]

theorem red_inf (hs : IsSeparated s) (i : X₀ ⟶ X) (k l : Chart s) :
    ∃ m, redOpen (chartOpen s) i m = redOpen (chartOpen s) i k ⊓ redOpen (chartOpen s) i l := by
  obtain ⟨m, hm⟩ := chart_inf hs k l
  exact ⟨m, by change i ⁻¹ᵁ m.1.1 = _; rw [hm]; rfl⟩

theorem Red.pull1 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull1 := by
  have a := tag_pull1 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa1 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull1 (chartOpen s)
  have d := tag_pull1 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H1.mk_surjective _ z
  rfl

theorem Red.pull2 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull2 := by
  have a := tag_pull2 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa2 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull2 (chartOpen s)
  have d := tag_pull2 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ z
  rfl

end Final

theorem crystallineDeRham : GlobalTheory.Published.CrystallineDeRham := fun _ _ _ _ hκ _ _ _ hπ hI _ _ _ _ _ hs hs' _ hp _ ↦
  ⟨Red.pull1 ⟨hκ, hπ, hI, hp⟩ hs hs', Red.pull2 ⟨hκ, hπ, hI, hp⟩ hs hs'⟩

end FubiniStudyChowHeightFormula₂.Adr
