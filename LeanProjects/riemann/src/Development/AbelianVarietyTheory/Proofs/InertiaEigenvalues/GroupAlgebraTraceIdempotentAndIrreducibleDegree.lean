import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.TrIdem

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem coeff_mul_zOf_one {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype _ _ (by simp)]
  simp only [tr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [zOf_coeff, mul_eq_one_iff_eq_inv', Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  ring

theorem trace_asAlgebraHom {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a) =
      tr a V.character := by
  simp only [tr, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, FDRep.character]
  rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp

theorem tr_idem_nat {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ)
    (ha : a * a = a) (hχ : IsChar χ) : ∃ n : ℕ, tr a χ = n := by
  obtain ⟨V, hV⟩ := hχ
  have hc : V.character = χ := funext hV
  set f := Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a with hf
  have hi : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf, ← map_mul, ha]
  refine ⟨Module.finrank ℂ (LinearMap.range f), ?_⟩
  rw [← hc, ← trace_asAlgebraHom, ← hf]
  exact (LinearMap.IsIdempotentElem.isProj_range f hi).trace

theorem irr_one_pos {G : Type} [Group G] (χ : G → ℂ) (hχ : IsIrr χ) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨V, hs, hV⟩ := hχ
  refine ⟨Module.finrank ℂ V, Nat.pos_of_ne_zero fun h => ?_, by rw [← hV, FDRep.char_one]⟩
  apply CategoryTheory.Simple.not_isZero V
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

end GlobalTheory.GLq.TrIdem

theorem GlobalTheory.GLq.trIdem : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ),
    (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧
      (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ :=
  fun _ _ _ a χ => ⟨GlobalTheory.GLq.TrIdem.tr_idem_nat a χ, GlobalTheory.GLq.TrIdem.irr_one_pos χ,
    GlobalTheory.GLq.TrIdem.coeff_mul_zOf_one a χ⟩
