import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
import Mathlib.FieldTheory.KummerExtension

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_product_polynomial_le (O N : Type) [CommRing O] [AddCommGroup N] [Module O N]
    (f : Module.End O N) (p : ℕ → Polynomial O) (s : Finset ℕ) :
    Module.length O (LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (LinearMap.ker (Polynomial.aeval f (p i))) ∧
    Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have key : ∀ g : Module.End O N, g = 1 →
        Module.length O (LinearMap.ker g) = 0 ∧ Module.length O (N ⧸ LinearMap.range g) = 0 := by
      rintro g rfl
      rw [Module.End.one_eq_id, LinearMap.ker_id, LinearMap.range_id]
      constructor <;> rw [Module.length_eq_zero_iff] <;> infer_instance
    obtain ⟨k1, k2⟩ := key (Polynomial.aeval f (∏ i ∈ (∅ : Finset ℕ), p i))
      (by rw [Finset.prod_empty, map_one])
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨k1.le, k2.le⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, map_mul]
    obtain ⟨h1, h2⟩ := lenComp O N (Polynomial.aeval f (p a)) (Polynomial.aeval f (∏ i ∈ s, p i))
    exact ⟨h1.trans (add_le_add le_rfl ih.1), h2.trans (add_le_add le_rfl ih.2)⟩

theorem UpperTheory.V.Base.lenRoots :
    ∀ (O N : Type) [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (n : ℕ) (ζ : O), 0 < n → IsPrimitiveRoot ζ n →
      ∀ f : Module.End O N, f ^ n = 1 →
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (LinearMap.ker (f - ζ ^ i • (1 : Module.End O N))) ∧
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (N ⧸ LinearMap.range (f - ζ ^ i • (1 : Module.End O N))) := by
  intro O N _ _ _ _ n ζ hn hζ f hf
  have hprod := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have hterm : ∀ i, Polynomial.aeval f (Polynomial.X - Polynomial.C (ζ ^ i * 1))
      = f - ζ ^ i • (1 : Module.End O N) := by
    intro i
    simp [Algebra.algebraMap_eq_smul_one, smul_pow]
  have e : Polynomial.aeval f (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))) = 0 := by
    rw [← hprod]
    simp [hf]
  have key : ∀ g : Module.End O N, g = 0 →
      Module.length O (LinearMap.ker g) = Module.length O N ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O N := by
    rintro g rfl
    rw [LinearMap.ker_zero, LinearMap.range_zero, Module.length_top,
      (Submodule.quotEquivOfEqBot (⊥ : Submodule O N) rfl).length_eq]
    exact ⟨rfl, rfl⟩
  have cong : ∀ g h : Module.End O N, g = h →
      Module.length O (LinearMap.ker g) = Module.length O (LinearMap.ker h) ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O (N ⧸ LinearMap.range h) := by
    rintro g h rfl
    exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := length_product_polynomial_le O N f (fun i => Polynomial.X - Polynomial.C (ζ ^ i * 1))
    (Finset.range n)
  obtain ⟨k1, k2⟩ := key _ e
  refine ⟨?_, ?_⟩
  · rw [← k1]
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).1))
  · rw [← k2]
    refine h2.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).2))
