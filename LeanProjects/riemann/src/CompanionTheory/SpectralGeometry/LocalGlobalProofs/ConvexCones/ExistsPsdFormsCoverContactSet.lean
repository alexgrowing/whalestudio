import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntEqZeroOfForallTwoPowDvd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFiniteBelowModTwo

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem finite_free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Module.Finite ℤ X ∧ Module.Free ℤ X := by
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hinj : Function.Injective s := fun x y h => by
    have := congrArg (Finsupp.linearCombination O id) h
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hinj ?_)
    rw [map_zero]
    ext c
    have h1 : r • s x = 0 := by
      rw [← map_zsmul s r x, hx, map_zero]
    have h2 : r • (s x c) = 0 := by simpa using DFunLike.congr_fun h1 c
    rw [zsmul_eq_mul] at h2
    have h3 : (r : O) ≠ 0 := by exact_mod_cast hr
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem exists_fin_reindex {T : Type} [Finite T] {X : Type} [AddCommGroup X] (m' : T → ℕ)
    (u' : ∀ t, Fin (m' t) → LinearMap.BilinForm ℤ X) (hsym : ∀ t i y z, u' t i y z = u' t i z y)
    (hnn : ∀ t i y, 0 ≤ u' t i y y) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∃ t, B ∈ rcone (u' t)) → ∃ j, B ∈ rcone (u j) := by
  obtain ⟨k, ⟨eq⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨k, fun j => m' (eq.symm j), fun j => u' (eq.symm j), fun j => hsym _, fun j => hnn _, ?_⟩
  rintro B ⟨t, ht⟩
  refine ⟨eq t, ?_⟩
  have key : ∀ t', t' = t → B ∈ rcone (u' t') := by
    rintro _ rfl
    exact ht
  exact key _ (eq.symm_apply_apply t)

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem isPosDef_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : IsPosDef B) :
    IsPosDef (pullR e.toLinearMap B) := by
  intro n x hx c hc
  let eZ : X ≃ₗ[ℤ] X := e.toAddEquiv.toIntLinearEquiv
  have h1 : LinearIndependent ℤ (fun i => e (x i)) := hx.map' eZ.toLinearMap eZ.ker
  simpa using hB n _ h1 c hc

theorem isMin2_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (hy : IsMin2 B y) :
    IsMin2 (pullR e.toLinearMap B) (e.symm y) := by
  intro x
  have := hy (e x)
  simpa [pullR_apply, map_add] using this

theorem exists_rcone_cover_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
    HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR ha
  obtain ⟨hfin, hfree⟩ := finite_free_int_of_projective O X
  obtain ⟨k, n, P, hsym, hnn, hcov⟩ := hR
  choose F hF hmin using fun j => finite_isMin2 X (n j) (P j) (hsym j) (hnn j)
  have hU : (⋃ j, F j).Finite := Set.finite_iUnion hF
  have hS := finite_addHom_of_covers2 X ι a ha _ hU
  let S : Set (X →+ X) := {f : X →+ X | ∀ i, f (a i) ∈ ⋃ j, F j}
  have hSf : Finite S := hS
  let form : ∀ (t : (Fin k) × S), Fin (n t.1) → LinearMap.BilinForm ℤ X := fun t i =>
    (P t.1 i).compl₁₂ t.2.1.toIntLinearMap t.2.1.toIntLinearMap
  obtain ⟨K, m, u, h1, h2, h3⟩ := exists_fin_reindex (T := Fin k × S) (fun t => n t.1) form
    (fun t i y z => hsym _ _ _ _) (fun t i y => hnn _ _ _)
  refine ⟨K, m, u, h1, h2, fun B hB hpos => h3 B ?_⟩
  obtain ⟨e, j, c, hc, hE⟩ := hcov B hB.1
  let f : X →+ X := e.symm.toLinearMap.toAddMonoidHom
  have hf : f ∈ S := fun i => Set.mem_iUnion.2 ⟨j, hmin j _ ⟨c, hc, hE⟩ (isPosDef_pullR e hpos) _ (isMin2_pullR e (hB.2 i))⟩
  refine ⟨(j, ⟨f, hf⟩), c, hc, LinearMap.ext₂ fun y z => ?_⟩
  have h4 := LinearMap.congr_fun₂ hE (f y) (f z)
  simpa [f, form, LinearMap.sum_apply] using h4

end GlobalTheory.CompanionTheory.Ar.Fan
