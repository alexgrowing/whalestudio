import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

section Lemmas

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem totExt_apply (x : Tot G) (j : ℕ) : totExt G E x j = G.toExt E j (x j) := rfl

theorem totExt_single (j : ℕ) (s : G.Sec j) :
    totExt G E (Pi.single j s) = Pi.single j (G.toExt E j s) := by
  funext k
  rw [totExt_apply]
  by_cases h : k = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem shift_totExt (u : Fin G.N → F) (x : Tot G) :
    shift (G.baseChange E) (fun k => algebraMap F E (u k)) (totExt G E x) = totExt G E (shift G u x) := by
  funext j
  cases j with
  | zero => rw [shift_apply_zero, totExt_apply, shift_apply_zero, map_zero]
  | succ j =>
    rw [shift_apply_succ, totExt_apply, totExt_apply, shift_apply_succ, Geo.toExt_mulW]
    rfl

end Lemmas

theorem totExt_props : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  intro F _ _ X Λ₀ E _ _ _
  refine ⟨?_, fun u x => shift_totExt X.toGeo E u x, ?_⟩
  · intro m v hv
    have hv' := hv.map' ((sysOf X Λ₀).V X.T).subtype (Submodule.ker_subtype _)
    have hform : ∀ i, ∃ y : X.toGeo.Sec X.T, (v i : Tot X.toGeo) = Pi.single X.T y := by
      intro i
      obtain ⟨y, hy⟩ := (v i).2
      exact ⟨y, hy.symm⟩
    choose f hf using hform
    have h1 : LinearIndependent F (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) := by
      have e : (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) = ((sysOf X Λ₀).V X.T).subtype ∘ v :=
        funext fun i => (hf i).symm
      rw [e]
      exact hv'
    have h2 := X.toGeo.linearIndependent_toExt E X.T m f h1.of_comp
    have h3 := h2.map' (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T)
      (LinearMap.ker_eq_bot.2 (Pi.single_injective _))
    have e2 : (fun i => totExt X.toGeo E (v i)) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T ∘ fun i => X.toGeo.toExt E X.T (f i)) := by
      funext i
      rw [hf i, totExt_single]
      rfl
    rw [e2]
    exact h3
  · intro j
    have hset : (totExt X.toGeo E '' ((sysOf X Λ₀).V j : Set (Tot X.toGeo))) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) j) ''
          (X.toGeo.toExt E j '' (X.V j : Set (X.toGeo.Sec j))) := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨_, ⟨y, y.2, rfl⟩, (totExt_single X.toGeo E j y).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, totExt_single X.toGeo E j y⟩
    rw [hset, ← Submodule.map_span]
    refine Eq.trans ?_ (LinearMap.range_comp ((X.baseChange E).V j).subtype (LinearMap.single E _ j)).symm
    rw [Submodule.range_subtype]
    rfl

end GlobalTheory.HSShort
