import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LNondomLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section NonDomMain

variable {R : Type*} [CommRing R] {r n : ℕ}

def ndEv (R : Type*) [CommRing R] (r n : ℕ) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun o => o.elim 0 X

lemma ndEv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (colAddGen R l j g) = g := by
  have : (ndEv R r n).comp (colAddGen R (r := r) l j) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, colAddGen, aeval_X, AlgHom.id_apply]
    split_ifs <;> simp [ndEv]
  exact congrArg (fun φ => φ g) this

lemma ndEv_pderiv_colAddGen (l j : Fin n) (g : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (pderiv none (colAddGen R l j g)) = ndE R r n l j g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [colAddGen, derivation_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, ndEv_colAddGen, ndEv_colAddGen, smul_eq_mul, smul_eq_mul]
    congr 1
    simp only [ndE, mkDerivation_X, colAddGen, aeval_X]
    split_ifs <;> simp [ndEv, Derivation.leibniz, pderiv_X]

lemma nd_pderiv_none_rename (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p v hp => simp [Derivation.leibniz, hp, pderiv_X]

lemma ndE_eq_zero {l j : Fin n} {f : MvPolynomial (Fin r × Fin n) R}
    (h : colAddGen R l j f = rename some f) : ndE R r n l j f = 0 := by
  rw [← ndEv_pderiv_colAddGen, h, nd_pderiv_none_rename, map_zero]

lemma nd_iter_Eul_l {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n l f = c • f) (k : ℕ) :
    ndEul R r n l ((ndF R r n l j)^[k] f) = (c - k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_l hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c - ((k : R) + 1) = (c - k) - 1 by ring, sub_smul (c - k) 1, one_smul]

lemma nd_iter_Eul_j {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n j f = c • f) (k : ℕ) :
    ndEul R r n j ((ndF R r n l j)^[k] f) = (c + k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_j hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c + ((k : R) + 1) = (c + k) + 1 by ring, add_smul (c + k) 1, one_smul]

lemma nd_iter_E {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {cl cj : R}
    (hl : ndEul R r n l f = cl • f) (hj : ndEul R r n j f = cj • f) (hE : ndE R r n l j f = 0)
    (k : ℕ) :
    ndE R r n l j ((ndF R r n l j)^[k + 1] f) =
      (((k : R) + 1) * (cl - cj - k)) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero =>
    rw [zero_add, Function.iterate_one, nd_comm_EF hlj, hE, map_zero, hl, hj]
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, one_mul, sub_zero]
    rw [sub_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (ndF R r n l j) (k + 1) f, nd_comm_EF hlj, ih,
      Derivation.map_smul, nd_iter_Eul_l hlj hl, nd_iter_Eul_j hlj hj,
      ← Function.iterate_succ_apply' (ndF R r n l j) k f, ← sub_smul, ← add_smul]
    congr 1
    push_cast; ring

theorem nd_main [IsDomain R] [CharZero R] (ν : Fin n → ℕ) {l j : Fin n} (hlj : l < j)
    (hν : ν l < ν j) (f : MvPolynomial (Fin r × Fin n) R)
    (hhom : IsWeightedHomogeneous (colW r n) f ν) (hinv : colAddGen R l j f = rename some f) :
    f = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := ndEul_homog (R := R) hhom l
  have hj := ndEul_homog (R := R) hhom j
  have hE := ndE_eq_zero hinv
  set G : ℕ → MvPolynomial (Fin r × Fin n) R := fun k => (ndF R r n l j)^[k] f with hG

  have hN : G (ν l + 1) = 0 := by
    apply ndEul_neg_eq_zero l
    rw [hG]; dsimp only
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (ν l : R) - ((ν l : R) + 1) = -1 by ring,
      neg_one_smul]

  have hstep : ∀ k, G (k + 1) = 0 → G k = 0 := by
    intro k hk
    have h1 := nd_iter_E hne hl hj hE k
    rw [show (ndF R r n l j)^[k + 1] f = G (k + 1) from rfl, hk, map_zero] at h1
    have hc : (((k : R) + 1) * ((ν l : R) - (ν j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (ν l : R) - (ν j : R) - k = (((ν l : ℤ) - ν j - k : ℤ) : R) := by push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ d k, G (k + d) = 0 → G k = 0 := by
    intro d
    induction d with
    | zero => intro k hk; simpa using hk
    | succ d ih =>
      intro k hk
      exact hstep k (ih (k + 1) (by rw [show k + 1 + d = k + (d + 1) by omega]; exact hk))
  have := hdown (ν l + 1) 0 (by simpa using hN)
  simpa [hG] using this

theorem dualWeylModuleNonDominant : DualWeylNonDom := by
  intro R _ _ _ r n ν ⟨l, j, hlj, hν⟩
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [dualWeyl, Submodule.mem_inf, mem_weightedHomogeneousSubmodule] at hf
  obtain ⟨hhom, hinv⟩ := hf
  have h1 := Submodule.mem_iInf _ |>.1 hinv l
  have h2 := Submodule.mem_iInf _ |>.1 h1 j
  have h3 := Submodule.mem_iInf _ |>.1 h2 hlj
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply] at h3
  exact nd_main ν hlj hν f hhom h3

end NonDomMain

end Formalism.GradedWeylDivisibility
