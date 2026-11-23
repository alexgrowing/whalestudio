import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.FirstOrderNbhd

theorem comp_app_eq_zero {E T U : Scheme.{0}} (c : E ⟶ U) (i' : T ⟶ E) (W : U.Opens)
    (a' : Γ(U, W)) (a : Γ(E, ⊤)) (h : c.app W a' = E.presheaf.map (homOfLE le_top).op a)
    (ha : i'.appTop a = 0) : (i' ≫ c).app W a' = 0 := by
  have ha0 : i'.app ⊤ a = 0 := ha
  have key : (i' ≫ c).app W a' = i'.app (c ⁻¹ᵁ W) (c.app W a') := by
    rw [Scheme.Hom.comp_app]
    try rfl
  have nat : i'.app (c ⁻¹ᵁ W) (E.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ W ≤ ⊤)).op a)
      = T.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ c ⁻¹ᵁ W ≤ ⊤)).op (i'.app ⊤ a) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.naturality, CategoryTheory.comp_apply]
    try rfl
  rw [key, h, nat, ha0]
  exact map_zero _

theorem exists_mem_ideal_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (W : U.affineOpens) (a : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) :
    ∃ a' ∈ e.ker.ideal W, (e.ker ^ 2).subschemeι.app W a' =
      (e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a := by
  obtain ⟨a', ha'⟩ := (e.ker ^ 2).subschemeι_app_surjective W
    ((e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a)
  refine ⟨a', ?_, ha'⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have h0 := comp_app_eq_zero (e.ker ^ 2).subschemeι i' (W : U.Opens) a' a ha' ha
  rw [hi] at h0
  exact h0

theorem mul_eq_zero_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (a b : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) (hb : i'.appTop b = 0) :
    a * b = 0 := by
  refine TopCat.Presheaf.section_ext (e.ker ^ 2).subscheme.sheaf ⊤ (a * b) 0 ?_
  intro x hx
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (e.ker ^ 2).subschemeι.base x) (U := ⊤) trivial
  let W' : U.affineOpens := ⟨W, hW⟩
  have hxW' : x ∈ (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) := hxW
  obtain ⟨a', ha'I, ha'⟩ := exists_mem_ideal_of_lift e i' hi W' a ha
  obtain ⟨b', hb'I, hb'⟩ := exists_mem_ideal_of_lift e i' hi W' b hb
  have hab : (e.ker ^ 2).subschemeι.app (W' : U.Opens) (a' * b') = 0 := by
    have hmem : a' * b' ∈ (e.ker ^ 2).ideal W' := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, sq]
      exact Ideal.mul_mem_mul ha'I hb'I
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hmem
    exact hmem
  have key : (e.ker ^ 2).subscheme.presheaf.map
      (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)).op (a * b) = 0 := by
    rw [map_mul, ← ha', ← hb', ← map_mul, hab]
  have h1 := TopCat.Presheaf.germ_res_apply (e.ker ^ 2).subscheme.presheaf
    (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)) x hxW' (a * b)
  rw [key, map_zero] at h1
  rw [map_zero]
  exact h1.symm

theorem ideal_sq_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U)
    [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme),
    i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤),
    i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  intro R _ U e _ i' hi a b ha hb
  exact mul_eq_zero_of_lift e i' hi a b ha hb

end GlobalTheory.CompanionTheory.FirstOrderNbhd
