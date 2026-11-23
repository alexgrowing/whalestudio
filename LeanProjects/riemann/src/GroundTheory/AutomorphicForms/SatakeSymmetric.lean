import Mathlib
import GroundTheory.AutomorphicForms.SphericalLaurent

noncomputable section

namespace GroundTheory.Automorphic

open AddMonoidAlgebra MvPolynomial

namespace Spherical

variable {n : ℕ}

def permCoord (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun l := l ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permCoord_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) : permCoord σ l = l ∘ σ.symm :=
  rfl

def permAct (σ : Equiv.Perm (Fin n)) : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ (permCoord σ)

theorem permAct_single (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (c : ℂ) :
    permAct σ (single l c) = single (l ∘ σ.symm) c := by
  simp [permAct, mapDomainAlgHom, mapDomain_single, permCoord_apply]

theorem permAct_mul (σ τ : Equiv.Perm (Fin n)) :
    permAct (σ * τ) = (permAct σ).comp (permAct τ) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, permAct_single, permAct_single, permAct_single]
  congr 1

theorem permAct_one : permAct (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (LaurentRing n) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [permAct_single, AlgHom.id_apply]
  rfl

theorem evalAt_permAct (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    evalAt w (permAct σ p) = evalAt (w ∘ σ) p := by
  have : (evalAt w).comp (permAct σ) = evalAt (w ∘ σ) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, permAct_single, evalAt_single, evalAt_single, monomialChar_apply,
      monomialChar_apply]
    congr 1
    exact Fintype.prod_equiv σ.symm _ _ fun i => by simp
  exact AlgHom.congr_fun this p

variable (n) in

def symmetricLaurent : Subalgebra ℂ (LaurentRing n) where
  carrier := {p | ∀ σ, permAct σ p = p}
  mul_mem' {a b} ha hb σ := by
    change permAct σ (a * b) = a * b
    rw [map_mul, ha σ, hb σ]
  add_mem' {a b} ha hb σ := by
    change permAct σ (a + b) = a + b
    rw [map_add, ha σ, hb σ]
  algebraMap_mem' c σ := AlgHom.commutes _ c

theorem mem_symmetricLaurent {p : LaurentRing n} :
    p ∈ symmetricLaurent n ↔ ∀ σ, permAct σ p = p :=
  Iff.rfl

theorem monomial_const_mem (c : ℤ) : monomial (fun _ : Fin n => c) ∈ symmetricLaurent n := by
  intro σ
  rw [permAct_single]
  rfl

def natToInt : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun s i := s i
  map_zero' := by
    funext i
    simp
  map_add' s t := by
    funext i
    simp

theorem natToInt_apply (s : Fin n →₀ ℕ) (i : Fin n) : natToInt s i = s i :=
  rfl

theorem natToInt_injective : Function.Injective (natToInt (n := n)) := fun s t h => by
  ext i
  exact Int.ofNat_inj.1 (congrFun h i)

variable (n) in

def polyEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] LaurentRing n :=
  mapDomainAlgHom ℂ ℂ natToInt

theorem polyEmb_monomial (s : Fin n →₀ ℕ) (c : ℂ) :
    polyEmb n (MvPolynomial.monomial s c) = single (natToInt s) c := by
  simp [polyEmb, mapDomainAlgHom, MvPolynomial.monomial, mapDomain_single]

theorem polyEmb_X (i : Fin n) : polyEmb n (X i) = monomial (Pi.single i 1) := by
  rw [X, polyEmb_monomial]
  congr 1
  funext j
  rw [natToInt_apply, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem polyEmb_injective : Function.Injective (polyEmb n) :=
  mapDomain_injective natToInt_injective

theorem polyEmb_rename (σ : Equiv.Perm (Fin n)) (Q : MvPolynomial (Fin n) ℂ) :
    polyEmb n (rename σ Q) = permAct σ (polyEmb n Q) := by
  have : (polyEmb n).comp (rename σ) = (permAct σ).comp (polyEmb n) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, polyEmb_X, polyEmb_X, permAct_single]
    congr 1
    funext j
    simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  exact AlgHom.congr_fun this Q

theorem mem_range_polyEmb {q : LaurentRing n} (hq : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i) :
    q ∈ (polyEmb n).range := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single q]
  refine Subalgebra.sum_mem _ fun l hl => ?_
  refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (l i).toNat) (q.coeff l), ?_⟩
  change polyEmb n _ = _
  rw [polyEmb_monomial]
  congr 1
  funext i
  simp [natToInt_apply, Int.toNat_of_nonneg (hq l hl i)]

theorem symmetricLaurent_le {A : Subalgebra ℂ (LaurentRing n)}
    (he : ∀ k, polyEmb n (esymm (Fin n) ℂ k) ∈ A) (hinv : monomial (fun _ => (-1 : ℤ)) ∈ A) :
    symmetricLaurent n ≤ A := by
  classical
  intro p hp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l ∈ p.coeff.support, ∀ i, -(N : ℤ) ≤ l i := by
    refine ⟨p.coeff.support.sup fun l => Finset.univ.sup fun i => (l i).natAbs, fun l hl i => ?_⟩
    have h1 : (l i).natAbs ≤ Finset.univ.sup fun i => (l i).natAbs :=
      Finset.le_sup (f := fun i => (l i).natAbs) (Finset.mem_univ i)
    have h2 := Finset.le_sup (f := fun l : Fin n → ℤ => Finset.univ.sup fun i => (l i).natAbs) hl
    have h3 : ((l i).natAbs : ℤ) ≤ _ := Nat.cast_le.2 (h1.trans h2)
    rw [Int.natCast_natAbs] at h3
    have h4 := neg_abs_le (l i)
    linarith
  set c : LaurentRing n := monomial (fun _ => (N : ℤ))
  set q := c * p
  have hq : q ∈ symmetricLaurent n := Subalgebra.mul_mem _ (monomial_const_mem _) hp
  have hqs : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i := by
    intro l hl i
    have hsub := AddMonoidAlgebra.support_coeff_mul_subset c p hl
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hsub
    have ha' : a = fun _ => (N : ℤ) := by
      have := Finsupp.support_single_subset ha
      simpa using this
    subst ha'
    have := hN b hb i
    simp only [Pi.add_apply]
    omega
  obtain ⟨Q, hQ⟩ := mem_range_polyEmb hqs
  change polyEmb n Q = q at hQ
  have hQsym : Q ∈ symmetricSubalgebra (Fin n) ℂ := by
    rw [mem_symmetricSubalgebra]
    intro σ
    apply polyEmb_injective
    rw [polyEmb_rename, hQ, hq σ]
  obtain ⟨P, hP⟩ := esymmAlgHom_surjective ℂ (σ := Fin n) (n := n) (Fintype.card_fin n).le ⟨Q, hQsym⟩
  have hQP : Q = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  have hqA : q ∈ A := by
    rw [← hQ, hQP, ← AlgHom.comp_apply, comp_aeval]
    have : aeval (fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))) P ∈
        (aeval fun i : Fin n => polyEmb n (esymm (Fin n) ℂ (i + 1))).range :=
      AlgHom.mem_range_self _ _
    rw [aeval_range] at this
    exact Algebra.adjoin_le (Set.range_subset_iff.2 fun i => he _) this
  have hp' : p = monomial (fun _ => (-1 : ℤ)) ^ N * q := by
    rw [AddMonoidAlgebra.single_pow, one_pow, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
      one_mul]
    have : (N • fun _ : Fin n => (-1 : ℤ)) + (fun _ => (N : ℤ)) = 0 := by
      funext i
      simp
    rw [this, ← AddMonoidAlgebra.one_def, one_mul]
  rw [hp']
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hinv _) hqA

def orbitSum (ν : Fin n → ℤ) : LaurentRing n :=
  ∑ σ : Equiv.Perm (Fin n), monomial (ν ∘ σ.symm)

theorem orbitSum_mem (ν : Fin n → ℤ) : orbitSum ν ∈ symmetricLaurent n := by
  intro τ
  rw [orbitSum, map_sum]
  simp only [permAct_single]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by congr 1

theorem coeff_orbitSum (ν l : Fin n → ℤ) :
    (orbitSum ν).coeff l = ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ν ∘ σ.symm = l).card : ℂ) := by
  classical
  rw [orbitSum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.card_filter,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem exists_of_coeff_orbitSum_ne_zero {ν l : Fin n → ℤ} (h : (orbitSum ν).coeff l ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ν ∘ σ.symm = l := by
  rw [coeff_orbitSum] at h
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.1 (fun h' => h (by rw [h', Nat.cast_zero]))
  exact ⟨σ, (Finset.mem_filter.1 hσ).2⟩

theorem coeff_orbitSum_self_ne_zero (ν : Fin n → ℤ) : (orbitSum ν).coeff ν ≠ 0 := by
  rw [coeff_orbitSum, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

theorem orbitSum_ne_zero (ν : Fin n → ℤ) : orbitSum ν ≠ 0 := fun h =>
  coeff_orbitSum_self_ne_zero ν (by rw [h]; rfl)

theorem comp_eq_of_antitone {ν : Fin n → ℤ} (hν : Antitone ν) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (ν ∘ σ)) : ν ∘ σ = ν := by
  set f : Fin n → ℤ := fun i => -ν i
  have hf : Monotone (f ∘ σ) := fun i j hij => neg_le_neg (hσ hij)
  have hf1 : Monotone (f ∘ (1 : Equiv.Perm (Fin n))) := fun i j hij => neg_le_neg (hν hij)
  have e1 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := σ)).2 hf
  have e2 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := 1)).2 hf1
  have : f ∘ σ = f := by
    rw [e1, ← e2]
    rfl
  funext i
  have := congrFun this i
  simpa [f] using this

end Spherical

end GroundTheory.Automorphic
