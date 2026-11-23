import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldAlternant

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra Finset

variable {n : ℕ}

def vPoly (m : ℕ) (t : ℂ) : ℂ := ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) / (1 - t)

theorem alternant_comp (μ : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    alternant (μ ∘ σ) = Equiv.Perm.sign σ • alternant μ := by
  have : monomial (μ ∘ σ) = permAct σ⁻¹ (monomial μ) := by
    rw [permAct_monomial]
    rfl
  rw [alternant, this, antisymm_permAct, Equiv.Perm.sign_inv]
  rfl

theorem exists_alternant_eq_smul {ν : Fin n → ℤ} (h0 : ∀ i, 0 ≤ ν i) (h1 : ∀ i, ν i ≤ n - 1) :
    ∃ c : ℂ, alternant ν = c • alternant (staircase n) := by
  by_cases hinj : Function.Injective ν
  · let f : Fin n → Fin n := fun i => ⟨n - 1 - (ν i).toNat, by
      have := h1 i; have := h0 i; have := i.2; omega⟩
    have hf : ∀ i, staircase n (f i) = ν i := by
      intro i
      simp only [staircase, f]
      have := h1 i; have := h0 i; have := i.2
      omega
    have hfi : Function.Injective f := fun i j h => hinj (by rw [← hf i, ← hf j, h])
    let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
    have hν : ν = staircase n ∘ σ := funext fun i => (hf i).symm
    refine ⟨((Equiv.Perm.sign σ : ℤ) : ℂ), ?_⟩
    rw [hν, alternant_comp, Units.smul_def, Int.cast_smul_eq_zsmul]
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    exact ⟨0, by rw [zero_smul, alternant_eq_zero hne hij]⟩

theorem card_pairs_containing_le (i : Fin n) :
    ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
      (fun p => p.1 = i ∨ p.2 = i)).card ≤ n - 1 := by
  classical
  let g : Fin n → Fin n × Fin n := fun j => if i < j then (i, j) else (j, i)
  have hsub : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).filter
      (fun p => p.1 = i ∨ p.2 = i) ⊆ (Finset.univ.erase i).image g := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hlt, h | h⟩ := hp
    · refine Finset.mem_image.2 ⟨p.2, Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_univ _⟩, ?_⟩
      · rw [h, h'] at hlt
        exact lt_irrefl _ hlt
      · simp only [g, ← h, if_pos hlt]
    · refine Finset.mem_image.2 ⟨p.1, Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_univ _⟩, ?_⟩
      · rw [h, h'] at hlt
        exact lt_irrefl _ hlt
      · simp only [g, ← h, if_neg (not_lt.2 hlt.le)]
  calc _ ≤ ((Finset.univ.erase i).image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase i).card := Finset.card_image_le
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

theorem coeff_prod_ne_zero (t : ℂ) (s : Finset (Fin n × Fin n)) :
    ∀ ν, (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff ν ≠ 0 →
      ∀ i, 0 ≤ ν i ∧ ν i ≤ (s.filter (fun p => p.1 = i ∨ p.2 = i)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ν hν i
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply] at hν
    split_ifs at hν with h
    · subst h
      simp
    · exact absurd rfl hν
  | insert a s ha ih =>
    intro ν hν i
    rw [Finset.prod_insert ha, sub_mul, smul_mul_assoc, AddMonoidAlgebra.coeff_sub,
      AddMonoidAlgebra.coeff_smul, Finsupp.sub_apply, Finsupp.smul_apply, varL, varL, monomial,
      monomial, AddMonoidAlgebra.coeff_single_mul_apply, AddMonoidAlgebra.coeff_single_mul_apply,
      one_mul, one_mul, smul_eq_mul] at hν
    have hcard : ((insert a s).filter (fun p => p.1 = i ∨ p.2 = i)).card =
        (if a.1 = i ∨ a.2 = i then 1 else 0) + (s.filter (fun p => p.1 = i ∨ p.2 = i)).card := by
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.1 h').1), add_comm]
      · simp
    rw [hcard]
    by_cases h1 : (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff (-Pi.single a.1 1 + ν) ≠ 0
    · have := ih _ h1 i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply] at this
      split_ifs at this ⊢ with h2 h3 h3 <;> simp_all <;> omega
    · push Not at h1
      rw [h1, zero_sub] at hν
      have h1' : (∏ p ∈ s, (varL p.1 - t • varL p.2) : LaurentRing n).coeff (-Pi.single a.2 1 + ν) ≠ 0 := by
        intro h
        rw [h, mul_zero, neg_zero] at hν
        exact hν rfl
      have := ih _ h1' i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply] at this
      split_ifs at this ⊢ with h2 h3 h3 <;> simp_all <;> omega

theorem coeff_hlFactor_ne_zero (t : ℂ) {ν : Fin n → ℤ} (hν : (hlFactor n t).coeff ν ≠ 0) (i : Fin n) :
    0 ≤ ν i ∧ ν i ≤ n - 1 := by
  have := coeff_prod_ne_zero t _ ν hν i
  refine ⟨this.1, this.2.trans ?_⟩
  have := card_pairs_containing_le i
  have hn : 0 < n := Fin.pos i
  omega

theorem exists_antisymm_hlFactor_eq (t : ℂ) :
    ∃ c : ℂ, antisymm n (hlFactor n t) = c • alternant (staircase n) := by
  classical
  have key : ∀ ν ∈ (hlFactor n t).coeff.support, ∃ c : ℂ,
      antisymm n (single ν ((hlFactor n t).coeff ν)) = c • alternant (staircase n) := by
    intro ν hν
    have hb := coeff_hlFactor_ne_zero t (Finsupp.mem_support_iff.1 hν)
    obtain ⟨c, hc⟩ := exists_alternant_eq_smul (fun i => (hb i).1) (fun i => (hb i).2)
    refine ⟨(hlFactor n t).coeff ν * c, ?_⟩
    have : (single ν ((hlFactor n t).coeff ν) : LaurentRing n) =
        (hlFactor n t).coeff ν • monomial ν := by
      simp [monomial, smul_single']
    rw [this, map_smul, ← alternant, hc, smul_smul]
  choose c hc using key
  refine ⟨∑ ν ∈ (hlFactor n t).coeff.support.attach, c ν.1 ν.2, ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (hlFactor n t)]
  rw [Finsupp.sum, map_sum, Finset.sum_smul, ← Finset.sum_attach]
  exact Finset.sum_congr rfl fun ν _ => hc ν.1 ν.2

theorem evalAt_varL (w : Fin n → ℂˣ) (a : Fin n) : evalAt w (varL a) = w a := by
  rw [varL, monomial, evalAt_single, one_mul, monomialChar_apply,
    Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun h => absurd (Finset.mem_univ a) h)]
  simp

theorem evalAt_hlFactor (w : Fin n → ℂˣ) (t : ℂ) :
    evalAt w (hlFactor n t) = ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 < p.2), ((w p.1 : ℂ) - t * w p.2) := by
  rw [hlFactor, map_prod]
  simp only [map_sub, map_smul, evalAt_varL, smul_eq_mul]

theorem evalAt_antisymm (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w (antisymm n p) = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (w ∘ σ) p := by
  rw [antisymm_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, evalAt_permAct, zsmul_eq_mul]

theorem alternant_staircase_eq_vdm (hn : 0 < n) :
    alternant (staircase n) =
      vdm.det * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : LaurentRing n) := by
  rw [staircase_eq_natCast, alternant_natCast_eq hn, remMat_staircase hn, Matrix.det_permutation]

theorem evalAt_vdm_det (w : Fin n → ℂˣ) :
    evalAt w vdm.det = (Matrix.vandermonde fun i => (w i : ℂ)).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [vdm, Matrix.of_apply, Matrix.vandermonde_apply, AlgHom.coe_toRingHom]
  rw [map_pow, evalAt_varL]

theorem strictMono_of_forall_succ_lt {f : Fin n → Fin n}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f i < f j) : StrictMono f := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → f a < f b := by
    intro d
    induction d with
    | zero => exact fun a b hab => h a b (by omega)
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d + 1 < n := by omega
      exact (ih a ⟨a + d + 1, hc⟩ rfl).trans (h _ b (by simp only; omega))
  intro a b hab
  exact key (b - a - 1) a b (by have := Fin.lt_def.1 hab; omega)

theorem eq_one_of_strictMono {τ : Equiv.Perm (Fin n)} (hτ : StrictMono τ) : τ = 1 := by
  have hinv : StrictMono τ.symm := by
    intro a b hab
    by_contra h
    rw [not_lt] at h
    have := hτ.monotone h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hab (not_lt.2 this)
  ext i
  have h1 : i ≤ τ i := hτ.le_apply
  have h2 : i ≤ τ.symm i := hinv.le_apply
  have h3 : τ i ≤ i := by
    have := hτ.monotone h2
    rwa [Equiv.apply_symm_apply] at this
  simp [le_antisymm h3 h1]

theorem exists_succ_of_ne_rev {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ Fin.revPerm) :
    ∃ a b : Fin n, a < b ∧ (σ b : ℕ) = σ a + 1 := by
  by_contra hne
  push Not at hne
  apply hσ

  have hmono : StrictMono (Fin.revPerm * σ⁻¹ : Equiv.Perm (Fin n)) := by
    refine strictMono_of_forall_succ_lt fun i j hij => ?_
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
    rcases lt_trichotomy (σ⁻¹ j) (σ⁻¹ i) with h | h | h
    · exact h
    · exact absurd (σ⁻¹.injective h) (fun h' => by rw [h'] at hij; omega)
    · have := hne _ _ h
      rw [show σ (σ⁻¹ j) = j from σ.apply_symm_apply j,
        show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at this
      omega
  have := eq_one_of_strictMono hmono
  rw [mul_eq_one_iff_eq_inv, inv_inv] at this
  rw [← this]

def revPoint (t : ℂ) (ht : t ≠ 0) : Fin n → ℂˣ := fun i => Units.mk0 (t ^ (n - 1 - (i : ℕ))) (pow_ne_zero _ ht)

theorem prod_one_sub_pow_shift (t : ℂ) (m : ℕ) :
    (∏ k ∈ Finset.range m, (1 - t ^ (k + 2))) * (1 - t) =
      (1 - t ^ (m + 1)) * ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_right_comm, ih]
    ring

theorem prod_pow_sub_pow_succ_mul (t : ℂ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1))) * (1 - t) =
      (1 - t ^ (m + 1)) * ∏ i ∈ Finset.range m, (t ^ i - t ^ m) := by
  have e1 : ∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1)) =
      (∏ i ∈ Finset.range m, t ^ i) * ∏ i ∈ Finset.range m, (1 - t ^ (m - 1 - i + 2)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  have e2 : ∏ i ∈ Finset.range m, (t ^ i - t ^ m) =
      (∏ i ∈ Finset.range m, t ^ i) * ∏ i ∈ Finset.range m, (1 - t ^ (m - 1 - i + 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [e1, e2, Finset.prod_range_reflect (fun k => 1 - t ^ (k + 2)) m,
    Finset.prod_range_reflect (fun k => 1 - t ^ (k + 1)) m, mul_assoc, prod_one_sub_pow_shift]
  ring

theorem vPoly_mul_pow (t : ℂ) (ht : t ≠ 1) (m : ℕ) :
    vPoly m t * (1 - t) ^ m = ∏ k ∈ Finset.range m, (1 - t ^ (k + 1)) := by
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  rw [vPoly, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    div_mul_cancel₀ _ (pow_ne_zero _ h1)]

theorem prod_pairs_pow_sub_eq_vPoly_mul (t : ℂ) (ht : t ≠ 1) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1)) =
      vPoly m t * ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) := by
  have h1 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  refine mul_right_cancel₀ (pow_ne_zero m h1) ?_
  rw [mul_right_comm, vPoly_mul_pow t ht]
  induction m with
  | zero => simp
  | succ m ih =>
    have htel := prod_pow_sub_pow_succ_mul t m
    rw [Finset.prod_range_succ (fun j => ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1))),
      Finset.prod_range_succ (fun k => 1 - t ^ (k + 1)),
      Finset.prod_range_succ (fun j => ∏ i ∈ Finset.range j, (t ^ i - t ^ j)), pow_succ (1 - t) m]
    calc _ = ((∏ j ∈ Finset.range m, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1))) * (1 - t) ^ m) *
          ((∏ i ∈ Finset.range m, (t ^ i - t ^ (m + 1))) * (1 - t)) := by ring
      _ = _ := by rw [ih, htel]; ring

theorem prod_pairs_eq_range (g : ℕ → ℕ → ℂ) :
    ∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p.1 p.2 =
      ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, g i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  rw [← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ Finset.range j, g i j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  dsimp only
  calc (∏ x : Fin n, if x < j then g x j else 1)
      = ∏ x : Fin n, (fun i : ℕ => if i < (j : ℕ) then g i j else 1) x :=
        Finset.prod_congr rfl fun x _ => by simp only [Fin.lt_def]
    _ = ∏ i ∈ Finset.range n, (if i < (j : ℕ) then g i j else 1) :=
        Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < (j : ℕ) then g i j else 1) n
    _ = ∏ i ∈ Finset.range j, g i j := by
        rw [← Finset.prod_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        have := j.2
        omega

theorem hlR_zero (t : ℂ) (ht : Function.Injective fun k : ℕ => t ^ k) :
    hlR t (0 : Fin n → ℤ) = algebraMap ℂ (LaurentRing n) (vPoly n t) := by
  have ht0 : t ≠ 0 := fun h => by
    have := @ht 1 2 (by simp [h])
    omega
  have ht1 : t ≠ 1 := fun h => by
    have := @ht 0 1 (by simp [h])
    omega
  have hne : ∀ a b : ℕ, a ≠ b → t ^ a - t ^ b ≠ 0 := fun a b h h' => h (ht (sub_eq_zero.1 h'))
  obtain ⟨c, hc⟩ := exists_antisymm_hlFactor_eq (n := n) t
  have hR : hlR t (0 : Fin n → ℤ) = algebraMap ℂ (LaurentRing n) c := by
    rw [hlR, show (monomial (0 : Fin n → ℤ) : LaurentRing n) = 1 from rfl, one_mul]
    refine altQuot_eq_of_mul ?_
    rw [hc, Algebra.smul_def, mul_comm]
  rw [hR]
  congr 1
  rcases n.eq_zero_or_pos with hn | hn
  · subst hn

    have hδ : alternant (staircase 0) = 1 := by
      rw [alternant, antisymm_apply, Fintype.sum_unique]
      simp only [Equiv.Perm.default_eq, Equiv.Perm.sign_one, one_smul]
      rw [permAct_one, AlgHom.id_apply,
        show staircase 0 = (0 : Fin 0 → ℤ) from funext fun i => i.elim0]
      rfl
    have hD : hlFactor 0 t = 1 := by
      rw [hlFactor]
      exact Finset.prod_eq_one fun p _ => p.1.elim0
    rw [hD, hδ, antisymm_apply, Fintype.sum_unique] at hc
    simp only [Equiv.Perm.sign_one, one_smul, map_one] at hc
    rw [vPoly, Finset.range_zero, Finset.prod_empty]
    have := congrArg (fun p : LaurentRing 0 => p.coeff 0) hc
    simp [AddMonoidAlgebra.one_def] at this
    exact this.symm

  set z : Fin n → ℂˣ := revPoint t ht0 with hz
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) with hP
  have hzv : ∀ k : Fin n, (z k : ℂ) = t ^ (n - 1 - (k : ℕ)) := fun k => rfl
  have hev := congrArg (evalAt z) hc
  rw [evalAt_antisymm, map_smul, alternant_staircase_eq_vdm hn, map_mul, map_intCast,
    evalAt_vdm_det, smul_eq_mul] at hev
  rw [Finset.sum_eq_single (Fin.revPerm : Equiv.Perm (Fin n))] at hev
  ·
    rw [evalAt_hlFactor] at hev
    have hA : ∏ p ∈ P, (((z ∘ Fin.revPerm) p.1 : ℂ) - t * (z ∘ Fin.revPerm) p.2) =
        ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ (j + 1)) := by
      rw [← prod_pairs_eq_range (n := n) (fun i j => t ^ i - t ^ (j + 1))]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [Function.comp_apply, hzv, Fin.revPerm_apply, Fin.val_rev]
      rw [← pow_succ']
      congr 2 <;> omega
    have hV : (Matrix.vandermonde fun i => (z i : ℂ)).det =
        ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) := by
      rw [Matrix.det_vandermonde, ← prod_pairs_eq_range (n := n) (fun i j => t ^ i - t ^ j)]
      rw [show (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((z j : ℂ) - z i)) =
          ∏ p ∈ P, ((z p.2 : ℂ) - z p.1) by
        rw [hP, Finset.prod_filter, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_filter]
        congr 1
        ext j
        simp]
      refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1))
        ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Fin.rev_lt_rev.2 hp
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact Fin.rev_lt_rev.2 hp
      · intro p _
        simp
      · intro p _
        simp
      · intro p _
        simp only [hzv, Fin.val_rev]
        congr 2 <;> omega
    rw [hA, hV] at hev
    have hs : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
        simp [h]
    have hVne : ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i hi =>
        hne i j (by have := Finset.mem_range.1 hi; omega)
    rw [prod_pairs_pow_sub_eq_vPoly_mul t ht1] at hev
    set V := ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (t ^ i - t ^ j)
    have h2 : (vPoly n t * V) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) =
        (c * V) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) := by
      rw [mul_comm _ ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ), hev]
      ring
    exact (mul_right_cancel₀ hVne (mul_right_cancel₀ hs h2)).symm
  ·
    intro σ _ hσ
    obtain ⟨a, b, hab, hσab⟩ := exists_succ_of_ne_rev hσ
    rw [evalAt_hlFactor, Finset.prod_eq_zero (i := (a, b)) (by simp [hP, hab]), mul_zero]
    simp only [Function.comp_apply, hzv]
    rw [← pow_succ']
    have := (σ b).2
    rw [show n - 1 - (σ b : ℕ) + 1 = n - 1 - (σ a : ℕ) by omega, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Spherical

end GroundTheory.Automorphic
