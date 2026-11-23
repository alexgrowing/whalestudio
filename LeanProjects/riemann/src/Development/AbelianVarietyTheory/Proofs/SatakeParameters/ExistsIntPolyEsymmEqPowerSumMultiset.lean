import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory.PowerSumPoly
open MvPolynomial

theorem exists_intPoly_psum_eq : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ,
    Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  intro a n _
  obtain ⟨Q, hQ⟩ := esymmAlgHom_surjective ℤ (σ := Fin a) (n := a) (by simp)
    ⟨psum (Fin a) ℤ n, psum_isSymmetric (Fin a) ℤ n⟩
  have hQ' : aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q = psum (Fin a) ℤ n := by
    rw [← esymmAlgHom_apply, hQ]
  refine ⟨rename Fin.succ Q, fun s hs => ?_⟩
  set f : Fin a → ℂ := fun i => s.toList[(i : ℕ)]'(by simp [hs]) with hf
  have hsf : (Finset.univ.val.map f) = s := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList s]
    congr 1
    apply List.ext_getElem (by simp [hs])
    intro i h1 h2
    simp [f]
  have key : aeval f (aeval (fun i : Fin a => esymm (Fin a) ℤ (i + 1)) Q) =
      aeval (fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1))) Q := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [hQ'] at key
  rw [aeval_rename]
  have lhs : (fun j : Fin (a + 1) => s.esymm j) ∘ Fin.succ = fun i : Fin a => aeval f (esymm (Fin a) ℤ (i + 1)) := by
    funext i
    simp [aeval_esymm_eq_multiset_esymm, hsf]
  rw [lhs, ← key]
  rw [psum, map_sum]
  simp only [map_pow, aeval_X]
  conv_rhs => rw [← hsf]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.PowerSumPoly
