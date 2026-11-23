import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SymmTensor

variable {n d : ℕ}

def tens (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∏ p, X p (I p) (K p)

def sym (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  ∑ π : Equiv.Perm (Fin d), tens (X ∘ π)

theorem tens_mul (X Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : tens X * tens Y = tens (X * Y) := by
  ext I K
  simp only [tens, Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem tens_one : tens (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I K
  simp only [tens, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem tens_single_apply (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Pi.mulSingle_eq_same]
  have : ∀ q ∈ Finset.univ.erase p, (Pi.mulSingle p Y : Fin d → Matrix (Fin n) (Fin n) ℂ) q (I q) (K q)
      = if I q = K q then 1 else 0 := fun q hq => by
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hq), Matrix.one_apply]
  rw [Finset.prod_congr rfl this, Finset.prod_ite_zero]
  simp

theorem sum_tens_single (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ a, ∑ b, Y a b • polar n d a b := by
  ext I K
  simp only [Matrix.sum_apply, tens_single_apply, polar, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : ∀ q, q ≠ p → I q = K q
  · simp [eq_true h, ite_and]
  · simp [eq_false h]

theorem sym_comp (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X :=
  Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl

theorem sym_mul (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    sym X * ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ i : Fin d, sym (X * Pi.mulSingle i Y) := by
  simp only [sym, Finset.sum_mul, Finset.mul_sum, tens_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Fintype.sum_equiv π _ _ fun p => ?_
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · have : π q ≠ π p := fun e => h (π.injective e)
    simp [h, this]

theorem sym_mem (X : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    sym X ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  suffices H : ∀ s : Finset (Fin d), ∀ X : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i ∉ s, X i = 1) → sym X ∈ A from
    H Finset.univ X (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X hX
    obtain rfl : X = 1 := funext fun i => hX i (by simp)
    refine A.sum_mem fun π _ => ?_
    rw [show (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) ∘ π = 1 from rfl, tens_one]
    exact A.one_mem
  | insert j s hj ih =>
    intro X hX
    set Z := Function.update X j 1 with hZ
    have hZ1 : ∀ i ∉ s, Z i = 1 := fun i hi => by
      by_cases h : i = j
      · subst h; simp [hZ]
      · rw [hZ, Function.update_of_ne h]; exact hX i (by simp [h, hi])
    have hP : ∑ p : Fin d, tens (Pi.mulSingle p (X j)) ∈ A := by
      rw [sum_tens_single]
      exact A.sum_mem fun a _ => A.sum_mem fun b _ => A.smul_mem (Algebra.subset_adjoin ⟨(a, b), rfl⟩) _
    have h1 := A.mul_mem (ih Z hZ1) hP
    rw [sym_mul, ← Finset.sum_add_sum_compl s] at h1
    have h2 : ∑ i ∈ s, sym (Z * Pi.mulSingle i (X j)) ∈ A := A.sum_mem fun i hi => ih _ fun k hk => by
      have : k ≠ i := fun e => hk (e ▸ hi)
      simp [hZ1 k hk, this]
    have h3 := A.sub_mem h1 h2
    have h4 : ∀ i ∈ sᶜ, sym (Z * Pi.mulSingle i (X j)) = sym X := fun i hi => by
      have hi : i ∉ s := by simpa using hi
      rw [← sym_comp X (Equiv.swap i j)]
      congr 1
      funext k
      by_cases hki : k = i
      · subst hki; simp [hZ1 k hi]
      · by_cases hkj : k = j
        · subst hkj
          simp [hZ, hki, hX i (by simp [hi, Ne.symm hki])]
        · simp [hZ, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [add_sub_cancel_left, Finset.sum_congr rfl h4, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
    have h5 : ((sᶜ.card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨j, by simpa using hj⟩)
    have := A.smul_mem h3 ((sᶜ.card : ℕ) : ℂ)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

theorem tens_unit_apply (I K I' K' : Fin d → Fin n) (π : Equiv.Perm (Fin d)) :
    tens ((fun p => Matrix.single (I p) (K p) (1 : ℂ)) ∘ π) I' K' =
      if I = I' ∘ π.symm then if K = K' ∘ π.symm then 1 else 0 else 0 := by
  simp only [tens, Matrix.of_apply, Function.comp_apply, Matrix.single_apply]
  rw [Finset.prod_ite_zero, ← ite_and]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one, forall_and, funext_iff, Function.comp_apply]
  refine if_congr (and_congr ?_ ?_) rfl rfl <;>
  exact ⟨fun h q => by simpa using h (π.symm q), fun h q => by simpa using h (π q)⟩

theorem mem_adjoin_polar (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  have h1 : ∀ (π : Equiv.Perm (Fin d)) I K, T (I ∘ π) (K ∘ π) = T I K := fun π I K => by
    have := congrFun (congrFun (hT π) (I ∘ π)) K
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      π.surjective.injective_comp_right.eq_iff] at this
    simpa using this
  have h2 : ∑ I, ∑ K, T I K • sym (fun p => Matrix.single (I p) (K p) (1 : ℂ)) = ((d.factorial : ℕ) : ℂ) • T := by
    ext I' K'
    simp only [sym, Matrix.sum_apply, Matrix.smul_apply, tens_unit_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp [h1, Fintype.card_perm]
  have h3 : ((d.factorial : ℕ) : ℂ) • T ∈ A :=
    h2 ▸ A.sum_mem fun I _ => A.sum_mem fun K _ => A.smul_mem (sym_mem _) _
  have h5 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have := A.smul_mem h3 ((d.factorial : ℕ) : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

end GlobalTheory.SymmTensor

end
