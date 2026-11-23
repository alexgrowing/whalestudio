import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteClassesOfTraceFormDualEq

namespace GlobalTheory.MarkedGenus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_fin_representatives {α β : Type*} [Finite β] (c : α → β) :
    ∃ (r : ℕ) (g : Fin r → α), ∀ a, ∃ j, c (g j) = c a := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range c)
  refine ⟨r, fun j => (e.symm j).2.choose, fun a => ⟨e ⟨c a, a, rfl⟩, ?_⟩⟩
  rw [(e.symm (e ⟨c a, a, rfl⟩)).2.choose_spec, Equiv.symm_apply_apply]

theorem finite_linearMap {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Finite N] : Finite (M →ₗ[R] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[R] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem finite_quotient_nsmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite ℤ R] [Module.Finite R M] {k : ℕ} (hk : 0 < k) :
    Finite (M ⧸ LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))) := by
  set P := LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))
  have hfin : Module.Finite ℤ (M ⧸ P) := Module.Finite.trans R (M ⧸ P)
  have hfg : AddGroup.FG (M ⧸ P) := Module.Finite.iff_addGroup_fg.mp hfin
  refine AddCommGroup.finite_of_fg_isAddTorsion _ (fun q => ?_)
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨k, hk, ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simp⟩

private lemma match_mod_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {k n : ℕ} (Dr : Fin n → Datum H) {A B : Datum H} (j1 j2 : Fin n)
    (e1 : A.La ≃ₗ[𝓞 E] (Dr j1).La) (e2 : B.La ≃ₗ[𝓞 E] (Dr j2).La)
    (he1 : ∀ x y, (Dr j1).EF (e1 x) (e1 y) = A.EF x y) (he2 : ∀ x y, (Dr j2).EF (e2 x) (e2 y) = B.EF x y)
    (fA : D.La →ₗ[𝓞 E] A.La) (fB : D.La →ₗ[𝓞 E] B.La)
    (h : (⟨j1, (LinearMap.range (k • (LinearMap.id : (Dr j1).La →ₗ[𝓞 E] (Dr j1).La))).mkQ.comp
        (e1.toLinearMap.comp fA)⟩ :
        Σ j : Fin n, D.La →ₗ[𝓞 E] ((Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La)))) =
      ⟨j2, (LinearMap.range (k • (LinearMap.id : (Dr j2).La →ₗ[𝓞 E] (Dr j2).La))).mkQ.comp
        (e2.toLinearMap.comp fB)⟩) :
    ∃ e : B.La ≃ₗ[𝓞 E] A.La, (∀ x y, A.EF (e x) (e y) = B.EF x y) ∧ ∀ x, ∃ y, e (fB x) = fA x + k • y := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  have hm := eq_of_heq hh
  refine ⟨e2.trans e1.symm, fun x y => ?_, fun x => ?_⟩
  · rw [← he1]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he2]
  · have hx := LinearMap.congr_fun hm x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at hx
    rw [Submodule.Quotient.eq] at hx
    obtain ⟨z, hz⟩ := hx
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz
    refine ⟨-(e1.symm z), e1.injective ?_⟩
    have h2 : e2 (fB x) = e1 (fA x) - k • z := by rw [hz]; abel
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add, map_neg, map_nsmul, h2,
      smul_neg, sub_eq_add_neg]

theorem finite_marked_data_in_genus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : ℕ) (ζ : ℂ), 0 < k → ∃ (r : ℕ) (Di : Fin r → Datum H) (fi : ∀ i, ℕ → D.La →ₗ[𝓞 E] (Di i).La) (νi : Fin r → ℕ → ℤ), (∀ i, ((Di i).p = D.p ∧ (Di i).q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, fi i (n * m) x = fi i n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, fi i n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = fi i n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ (Di i).EF (fi i n x) (fi i n x') - νi i n * D.EF x x') ∧ ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (νi i k : ℂ) / k)) ∧ ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → ∃ (i : Fin r) (e : D'.La ≃ₗ[𝓞 E] (Di i).La), (∀ x y, (Di i).EF (e x) (e y) = D'.EF x y) ∧ ∀ x, ∃ y, e (f k x) = fi i k x + k • y := by
  intro E _ _ _ H D k ζ hk
  obtain ⟨n, Dr, hDr, hcls⟩ := GlobalTheory.DatumClasses.finite_data_of_signature E H D.p D.q
  let Q : Fin n → Type := fun j =>
    (Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La))
  have hQ : ∀ j, Finite (D.La →ₗ[𝓞 E] Q j) := fun j => by
    have := D.fin
    have := (Dr j).fin
    have : Finite (Q j) := finite_quotient_nsmul hk
    exact finite_linearMap
  let Cond : (D' : Datum H) → (ℕ → D.La →ₗ[𝓞 E] D'.La) → (ℕ → ℤ) → Prop := fun D' f ν =>
    (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
    ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k)
  let α := {a : Σ D' : Datum H, (ℕ → D.La →ₗ[𝓞 E] D'.La) × (ℕ → ℤ) // Cond a.1 a.2.1 a.2.2}
  choose jf ef hef using fun a : α => hcls a.1.1 a.2.1.1 a.2.1.2.1
  let c : α → Σ j : Fin n, (D.La →ₗ[𝓞 E] Q j) := fun a =>
    ⟨jf a, (LinearMap.range (k • (LinearMap.id : (Dr (jf a)).La →ₗ[𝓞 E] (Dr (jf a)).La))).mkQ.comp
      ((ef a).toLinearMap.comp (a.1.2.1 k))⟩
  obtain ⟨r, g, hg⟩ := exists_fin_representatives c
  refine ⟨r, fun i => (g i).1.1, fun i => (g i).1.2.1, fun i => (g i).1.2.2, fun i => (g i).2, ?_⟩
  intro D' f ν hc hζ
  obtain ⟨i, hi⟩ := hg ⟨⟨D', f, ν⟩, hc, hζ⟩
  exact ⟨i, match_mod_lemma Dr _ _ (ef (g i)) (ef ⟨⟨D', f, ν⟩, hc, hζ⟩) (hef (g i)) (hef _) _ _ hi⟩

end GlobalTheory.MarkedGenus
