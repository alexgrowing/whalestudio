import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValuesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_list (k : Type) [CommRing k] (D : ℕ) (L : ℕ) :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsArithVar p D →
    ∀ (g : List X.functionField), g.length = L → (∀ h ∈ g, h ≠ 0) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField),
      IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ h ∈ g, ∀ y : Y, RegAt y (φ h) ∨ RegAt y (φ h)⁻¹ := by
  induction L with
  | zero =>
    intro X _ p hp g hg _
    obtain rfl := List.length_eq_zero_iff.1 hg
    refine ⟨X, inferInstance, 𝟙 X, RingHom.id _, by simpa using hp, (GlobalTheory.T.isBirationalModel_id_and_comp X X X (𝟙 X) (𝟙 X)
      (RingHom.id _) (RingHom.id _)).1, by simp⟩
  | succ n ih =>
    intro X _ p hp g hg hne
    obtain ⟨a, g', rfl⟩ : ∃ a g', g = a :: g' := by
      cases g with
      | nil => simp at hg
      | cons a g' => exact ⟨a, g', rfl⟩
    obtain ⟨Y₁, hY₁, π₁, φ₁, hA₁, hM₁, hR₁⟩ :=
      ih X p hp g' (by simpa using hg) (fun h hh => hne h (List.mem_cons_of_mem _ hh))
    have ha : φ₁ a ≠ 0 := (map_ne_zero φ₁).2 (hne a List.mem_cons_self)
    obtain ⟨Y₂, hY₂, π₂, φ₂, hA₂, hM₂, hR₂⟩ := GlobalTheory.T.exists_blowup_model_regular_function_or_inverse k Y₁ (π₁ ≫ p) D hA₁ (φ₁ a) ha
    refine ⟨Y₂, hY₂, π₂ ≫ π₁, φ₂.comp φ₁, by simpa [Category.assoc] using hA₂,
      (GlobalTheory.T.isBirationalModel_id_and_comp X Y₁ Y₂ π₁ π₂ φ₁ φ₂).2 hM₁ hM₂, ?_⟩
    have hreg := (GlobalTheory.T.birationalModel_regular_unit_values k Y₁ Y₂ (π₁ ≫ p) (π₂ ≫ π₁ ≫ p) π₂ rfl φ₂ hM₂).1
    intro h hh y
    rcases List.mem_cons.1 hh with rfl | hh
    · simpa using hR₂ y
    · rcases hR₁ h hh (π₂ y) with h1 | h1
      · exact Or.inl (by simpa using hreg y _ h1)
      · exact Or.inr (by simpa [map_inv₀] using hreg y _ h1)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_total : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  intro k _ X _ p D hp J _ f hf
  have := Fintype.ofFinite J
  let g : List X.functionField := (Finset.univ : Finset (J × J)).toList.map (fun q => f q.1 / f q.2)
  have hg : ∀ j l, f j / f l ∈ g := fun j l => by
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨(j, l), rfl⟩
  obtain ⟨Y, hY, π, φ, hA, hM, hR⟩ := exists_model_list k D g.length X p hp g rfl (by
    intro h hh
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hh
    obtain ⟨q, rfl⟩ := hh
    exact div_ne_zero (hf q.1) (hf q.2))
  refine ⟨Y, hY, π, φ, hA, hM, fun j => (map_ne_zero φ).2 (hf j), fun y j l => ?_⟩
  rcases hR _ (hg j l) y with h | h
  · exact Or.inl (by simpa [map_div₀] using h)
  · exact Or.inr (by simpa [map_div₀, inv_div] using h)

end GlobalTheory.HSNef
