import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE
import GroundTheory.AutomorphicForms.HarishChandraCentre.RepBase

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def rhoDeriv (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) :
    Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2))

theorem rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (a : Fin n × Fin n) :
    rhoDeriv c M (X a) = ∑ i, C (M i a.1) * (X (i, a.2) + C (c i a.2)) :=
  mkDerivation_X ℂ _ a

theorem rhoDeriv_add (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c (M + N) = rhoDeriv c M + rhoDeriv c N := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.add_apply, Matrix.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

theorem rhoDeriv_smul (c : Matrix (Fin n) (Fin n) ℂ) (r : ℂ) (M : gl n) :
    rhoDeriv c (r • M) = r • rhoDeriv c M := by
  apply derivation_ext
  intro a
  simp only [rhoDeriv_X, Derivation.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem rhoDeriv_rhoDeriv_X (c : Matrix (Fin n) (Fin n) ℂ) (P Q : gl n) (a : Fin n × Fin n) :
    rhoDeriv c P (rhoDeriv c Q (X a)) =
      ∑ k, C ((P * Q) k a.1) * (X (k, a.2) + C (c k a.2)) := by
  rw [rhoDeriv_X, map_sum]
  simp only [Derivation.leibniz, Derivation.map_add, derivation_C, smul_zero, add_zero,
    smul_eq_mul, mul_zero, rhoDeriv_X, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  ring

theorem rhoDeriv_lie (c : Matrix (Fin n) (Fin n) ℂ) (M N : gl n) :
    rhoDeriv c ⁅M, N⁆ = ⁅rhoDeriv c M, rhoDeriv c N⁆ := by
  apply derivation_ext
  intro a
  rw [Derivation.commutator_apply, rhoDeriv_rhoDeriv_X, rhoDeriv_rhoDeriv_X, rhoDeriv_X,
    LieRing.of_associative_ring_bracket]
  simp only [Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

noncomputable def rhoLie (c : Matrix (Fin n) (Fin n) ℂ) : gl n →ₗ⁅ℂ⁆ Module.End ℂ (Poly n) where
  toFun M := (rhoDeriv c M : Poly n →ₗ[ℂ] Poly n)
  map_add' M N := by rw [rhoDeriv_add]; rfl
  map_smul' r M := by rw [rhoDeriv_smul]; rfl
  map_lie' {M N} := by
    rw [rhoDeriv_lie, Derivation.commutator_coe_linear_map]

noncomputable def rho (c : Matrix (Fin n) (Fin n) ℂ) : U n →ₐ[ℂ] Module.End ℂ (Poly n) :=
  UniversalEnvelopingAlgebra.lift ℂ (rhoLie c)

theorem rho_ι_apply (c : Matrix (Fin n) (Fin n) ℂ) (M : gl n) (f : Poly n) :
    rho c (UniversalEnvelopingAlgebra.ι ℂ M) f = rhoDeriv c M f := by
  simp [rho, rhoLie]

theorem rho_e_apply (c : Matrix (Fin n) (Fin n) ℂ) (a : Fin n × Fin n) (f : Poly n) :
    rho c (e a) f = rhoDeriv c (E a) f :=
  rho_ι_apply c (E a) f

theorem rhoDeriv_E_X (c : Matrix (Fin n) (Fin n) ℂ) (i j a b : Fin n) :
    rhoDeriv c (E (i, j)) (X (a, b)) = if a = j then X (i, b) + C (c i b) else 0 := by
  rw [rhoDeriv_X, Finset.sum_eq_single i]
  · by_cases h : a = j
    · subst h; simp [E]
    · simp [E, Matrix.single_apply, Ne.symm h, h]
  · intro k _ hk
    simp [E, Matrix.single_apply, Ne.symm hk]
  · simp

noncomputable def rowDeriv (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ fun a => if a.1 = j then X (i, a.2) else 0

theorem rowDeriv_apply (i j : Fin n) (f : Poly n) : rowDeriv i j f = rowOp i j f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowDeriv, rowOp_apply, derivation_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p a hp =>
    rw [Derivation.leibniz, hp, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul]
    have h1 : rowDeriv i j (X a) = ∑ k, X (i, k) * pderiv (j, k) (X a) := by
      obtain ⟨a1, a2⟩ := a
      simp only [rowDeriv, mkDerivation_X, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      rw [Finset.sum_eq_single a2]
      · by_cases h : a1 = j <;> simp [h]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    rw [h1]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

theorem rhoDeriv_zero_E (i j : Fin n) : rhoDeriv 0 (E (i, j)) = rowDeriv i j := by
  apply derivation_ext
  rintro ⟨a, b⟩
  rw [rhoDeriv_E_X]
  simp [rowDeriv, mkDerivation_X]

theorem rho_zero_e (i j : Fin n) : rho 0 (e (i, j)) = rowOp i j := by
  refine LinearMap.ext fun f => ?_
  rw [rho_e_apply, rhoDeriv_zero_E, rowDeriv_apply]

theorem rho_one_e_apply (i j : Fin n) (f : Poly n) :
    rho 1 (e (i, j)) f = pderiv (j, i) f + rowOp i j f := by
  rw [rho_e_apply, ← rowDeriv_apply, ← Derivation.add_apply]
  congr 1
  apply derivation_ext
  rintro ⟨a, b⟩
  rw [rhoDeriv_E_X, Derivation.add_apply, pderiv_X]
  simp only [rowDeriv, mkDerivation_X, Matrix.one_apply, Pi.single_apply, Prod.mk.injEq]
  by_cases h : a = j
  · subst h
    by_cases h' : b = i
    · subst h'; simp [add_comm]
    · simp [h'] <;> exact fun hh => h' hh.symm
  · simp [h]

noncomputable def shift : Poly n ≃ₐ[ℂ] Poly n :=
  AlgEquiv.ofAlgHom (aeval fun a => X a + C (if a.1 = a.2 then 1 else 0))
    (aeval fun a => X a - C (if a.1 = a.2 then 1 else 0))
    (by ext a : 1; simp) (by ext a : 1; simp)

theorem shift_X (a : Fin n × Fin n) : shift (X a : Poly n) = X a + C (if a.1 = a.2 then 1 else 0) := by
  simp [shift]

theorem shift_C (r : ℂ) : shift (C r : Poly n) = C r :=
  (shift : Poly n ≃ₐ[ℂ] Poly n).commutes r

theorem rhoDeriv_one_shift (M : gl n) (f : Poly n) :
    rhoDeriv 1 M (shift f) = shift (rhoDeriv 0 M f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    have : shift (C r : Poly n) = C r := (shift : Poly n ≃ₐ[ℂ] Poly n).commutes r
    rw [this, derivation_C, derivation_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p a hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    congr 2
    rw [shift_X, Derivation.map_add, derivation_C, add_zero, rhoDeriv_X, rhoDeriv_X, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [shift_X, shift_C, Matrix.one_apply]

theorem rho_one_shift (u : U n) (f : Poly n) : rho 1 u (shift f) = shift (rho 0 u f) := by
  induction u using U.induction generalizing f with
  | halg r => simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | hι M => rw [rho_ι_apply, rho_ι_apply, rhoDeriv_one_shift]
  | hmul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
  | hadd a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb,
      map_add]

theorem rho_one_eq_zero_of_rho_zero_eq_zero (u : U n) (h : rho 0 u = 0) : rho 1 u = 0 := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨g, rfl⟩ := (shift : Poly n ≃ₐ[ℂ] Poly n).surjective f
  rw [rho_one_shift, h, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

def geDeg (t : ℕ) : Submodule ℂ (Poly n) where
  carrier := {f | ∀ s : Fin n × Fin n →₀ ℕ, s.degree < t → coeff s f = 0}
  add_mem' {f g} hf hg s hs := by rw [coeff_add, hf s hs, hg s hs, add_zero]
  zero_mem' s _ := coeff_zero s
  smul_mem' r f hf s hs := by rw [coeff_smul, hf s hs, smul_zero]

theorem geDeg_anti {t t' : ℕ} (h : t' ≤ t) : (geDeg t : Submodule ℂ (Poly n)) ≤ geDeg t' :=
  fun _ hf s hs => hf s (lt_of_lt_of_le hs h)

theorem monomial_mem_geDeg {t : ℕ} (s : Fin n × Fin n →₀ ℕ) (c : ℂ) (h : t ≤ s.degree) :
    (monomial s c : Poly n) ∈ geDeg t := by
  intro s' hs'
  rw [coeff_monomial, if_neg]
  rintro rfl
  omega

theorem constantCoeff_eq_zero_of_mem_geDeg {f : Poly n} (hf : f ∈ geDeg 1) :
    constantCoeff f = 0 := by
  have h0 : constantCoeff f = coeff 0 f := by rw [constantCoeff_eq]
  rw [h0]
  exact hf 0 (by simp)

theorem mem_geDeg_of_isHomogeneous {f : Poly n} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ geDeg d := by
  intro s hs
  by_contra h
  have h2 : s.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hf h
  omega

theorem map_mem_of_monomial (L : Poly n →ₗ[ℂ] Poly n) (P : Submodule ℂ (Poly n))
    (Q : (Fin n × Fin n →₀ ℕ) → Prop) {f : Poly n} (hf : ∀ s, coeff s f ≠ 0 → Q s)
    (h : ∀ s (c : ℂ), Q s → L (monomial s c) ∈ P) : L f ∈ P := by
  rw [f.as_sum, map_sum]
  exact Submodule.sum_mem _ fun s hs => h s _ (hf s (mem_support_iff.1 hs))

theorem degree_sub_single {s : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n} (h : s a ≠ 0) :
    (s - Finsupp.single a 1).degree + 1 = s.degree := by
  have hle : Finsupp.single a 1 ≤ s := by
    rw [Finsupp.single_le_iff]; omega
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

theorem pderiv_monomial_mem_geDeg {t : ℕ} (a : Fin n × Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : pderiv a (monomial s c : Poly n) ∈ geDeg (t - 1) := by
  rw [pderiv_monomial]
  by_cases hs : s a = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · apply monomial_mem_geDeg
    have := degree_sub_single hs
    omega

theorem pderiv_mem_geDeg {t : ℕ} (a : Fin n × Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    pderiv a f ∈ geDeg (t - 1) := by
  refine map_mem_of_monomial (pderiv a : Derivation ℂ (Poly n) (Poly n)).toLinearMap _
    (fun s => t ≤ s.degree) (fun s hs => ?_) (fun s c hs => pderiv_monomial_mem_geDeg a s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))

theorem rowOp_monomial (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i j (monomial s c) =
      ∑ k, monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) := by
  rw [rowOp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]

theorem rowOp_monomial_term_mem {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (c : ℂ)
    (P : Submodule ℂ (Poly n))
    (h : s (j, k) ≠ 0 → (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1))
        (c * s (j, k)) : Poly n) ∈ P) :
    (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) : Poly n)
      ∈ P := by
  by_cases hs : s (j, k) = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · exact h hs

theorem degree_rowOp_term {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (hs : s (j, k) ≠ 0) :
    (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)).degree = s.degree := by
  rw [map_add, Finsupp.degree_single, ← degree_sub_single hs]
  ring

theorem rowOp_monomial_mem_geDeg {t : ℕ} (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : rowOp i j (monomial s c) ∈ geDeg t := by
  rw [rowOp_monomial]
  refine Submodule.sum_mem _ fun k _ => rowOp_monomial_term_mem c _ fun hs => ?_
  apply monomial_mem_geDeg
  rw [degree_rowOp_term hs]; exact h

theorem rowOp_mem_geDeg {t : ℕ} (i j : Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    rowOp i j f ∈ geDeg t := by
  refine map_mem_of_monomial (rowOp i j) _ (fun s => t ≤ s.degree) (fun s hs => ?_)
    (fun s c hs => rowOp_monomial_mem_geDeg i j s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))

noncomputable def iterPd (w : List (Fin n × Fin n)) (f : Poly n) : Poly n :=
  w.foldr (fun a g => pderiv (a.2, a.1) g) f

@[simp] theorem iterPd_nil (f : Poly n) : iterPd [] f = f := rfl

@[simp] theorem iterPd_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) (f : Poly n) :
    iterPd (a :: w) f = pderiv (a.2, a.1) (iterPd w f) := rfl

theorem iterPd_mem_geDeg (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n} (hf : f ∈ geDeg t) :
    iterPd w f ∈ geDeg (t - w.length) := by
  induction w with
  | nil => simpa using hf
  | cons a w ih =>
    rw [iterPd_cons, List.length_cons, ← Nat.sub_sub]
    exact pderiv_mem_geDeg _ ih

theorem rho_one_word_sub_iterPd (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n}
    (hw : w.length ≤ t) (hf : f ∈ geDeg t) :
    rho 1 (word w) f - iterPd w f ∈ geDeg (t - w.length + 1) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.length_cons] at hw ⊢
    have ih := ih (by omega)
    rw [word_cons, map_mul, Module.End.mul_apply, iterPd_cons]
    obtain ⟨i, j⟩ := a
    rw [rho_one_e_apply]
    set g := rho 1 (word w) f
    have e1 : pderiv (j, i) g + rowOp i j g - pderiv (j, i) (iterPd w f) =
        pderiv (j, i) (g - iterPd w f) + rowOp i j (g - iterPd w f) + rowOp i j (iterPd w f) := by
      rw [map_sub, map_sub]; abel
    rw [e1]
    have ht : t - (w.length + 1) + 1 = t - w.length := by omega
    rw [ht]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have := pderiv_mem_geDeg (j, i) ih
      rwa [Nat.add_sub_cancel] at this
    · exact geDeg_anti (by omega) (rowOp_mem_geDeg i j ih)
    · exact rowOp_mem_geDeg i j (iterPd_mem_geDeg w hf)

theorem constantCoeff_rho_one_word_of_lt (w : List (Fin n × Fin n)) (f : Poly n) (d : ℕ)
    (hf : f.IsHomogeneous d) (h : w.length < d) :
    constantCoeff (rho 1 (word w) f) = 0 := by
  have hf' := mem_geDeg_of_isHomogeneous hf
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  have h2 := iterPd_mem_geDeg w hf'
  rw [← sub_add_cancel (rho 1 (word w) f) (iterPd w f), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1),
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h2), add_zero]

theorem toFinsupp_map_swap_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp (((a :: w).map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      Finsupp.single (a.2, a.1) 1 +
        Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) := by
  rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]
  rfl

theorem iterPd_monomial (w : List (Fin n × Fin n)) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    ∃ κ : ℂ, iterPd w (monomial s c) =
        monomial (s - Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _)) (c * κ) ∧
      (κ ≠ 0 ↔ Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) ≤ s) := by
  induction w with
  | nil => exact ⟨1, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨κ, h1, h2⟩ := ih
    rw [toFinsupp_map_swap_cons]
    generalize Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) = T
      at h1 h2 ⊢
    refine ⟨κ * ((s - T) (a.2, a.1) : ℕ), ?_, ?_⟩
    · rw [iterPd_cons, h1, pderiv_monomial, tsub_tsub, add_comm T, mul_assoc]
    · rw [mul_ne_zero_iff, h2, Nat.cast_ne_zero, Finsupp.tsub_apply]
      constructor
      · rintro ⟨hT, hb⟩ x
        rw [Finsupp.add_apply, Finsupp.single_apply]
        have := hT x
        split_ifs with hx
        · subst hx; omega
        · omega
      · intro h
        have hx : ∀ x, T x ≤ s x := fun x => le_trans (by simp) (h x)
        refine ⟨hx, ?_⟩
        have := h (a.2, a.1)
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega

theorem constantCoeff_rho_one_word_monomial (w : List (Fin n × Fin n))
    (s : Fin n × Fin n →₀ ℕ) (h : w.length = s.degree) :
    constantCoeff (rho 1 (word w) (monomial s 1)) ≠ 0 ↔
      Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) = s := by
  have hf' : (monomial s (1 : ℂ) : Poly n) ∈ geDeg s.degree := monomial_mem_geDeg s 1 le_rfl
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  rw [← sub_add_cancel (rho 1 (word w) (monomial s 1)) (iterPd w (monomial s 1)), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1), zero_add]
  obtain ⟨κ, hκ, hiff⟩ := iterPd_monomial w s 1
  rw [hκ, constantCoeff_monomial, one_mul]
  set T := Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n))
  constructor
  · intro hne
    split_ifs at hne with h0
    · exact le_antisymm (hiff.1 hne) (tsub_eq_zero_iff_le.1 h0)
    · exact absurd rfl hne
  · rintro rfl
    rw [tsub_self, if_pos rfl]
    exact hiff.2 le_rfl

end GroundTheory.Automorphic.HarishChandra
