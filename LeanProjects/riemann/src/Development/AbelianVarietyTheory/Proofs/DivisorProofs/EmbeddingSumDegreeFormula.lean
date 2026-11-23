import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem card_embeddings_restrict_eq_finrank (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Algebra k k'] (τ : k →+* ℂ) :
    Nat.card {σ : k' →+* ℂ // σ.comp (algebraMap k k') = τ} = Module.finrank k k' := by
  letI : Algebra k ℂ := τ.toAlgebra
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← AlgHom.card k k' ℂ, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
    fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩

theorem finrank_mul_sum_embeddings_comp (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    (i : k →+* k') (f : (k →+* ℂ) → ℝ) :
    (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i)
      = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  classical
  letI : Algebra k k' := i.toAlgebra
  have h1 : ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank k k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : k' →+* ℂ => σ.comp i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f τ) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
      Finset.sum_const, nsmul_eq_mul, ← card_embeddings_restrict_eq_finrank k k' τ,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h1, ← _root_.mul_assoc, ← Module.finrank_mul_finrank ℚ k k', Nat.cast_mul]

end GlobalTheory
