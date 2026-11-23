import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem prod_X_sub_C_dvd_pow_of_isRoot (g : ℂ[X]) :
    ∀ s : Multiset ℂ, (∀ a ∈ s, g.IsRoot a) →
      (s.map fun a => X - C a).prod ∣ g ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s)))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

theorem dvd_pow_natDegree_of_forall_isRoot (f g : ℂ[X]) (hf : f.Monic)
    (h : ∀ a ∈ f.roots, g.IsRoot a) : f ∣ g ^ f.natDegree := by
  have hc : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have key := prod_X_sub_C_dvd_pow_of_isRoot g f.roots h
  rw [hc] at key
  have hf' := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [hf.leadingCoeff, C_1, one_mul] at hf'
  rwa [hf'] at key

theorem exists_poly_pow_mul_eq_one : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B →
    ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  intro n l B hl hB
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  set f := B.charpoly with hf
  have hfm : f.Monic := Matrix.charpoly_monic B
  have hB0 : aeval B f = 0 := Matrix.aeval_self_charpoly B
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
  have hroot0 : ∀ a ∈ f.roots, a ≠ 0 := by
    intro a ha h0
    subst h0
    have h1 : f.eval 0 = 0 := (mem_roots hfm.ne_zero).mp ha
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, ← hf, h1, mul_zero]
  have hc : ∀ a : ℂ, ∃ c : ℂ, a ≠ 0 → c ^ (k + 1) * a = 1 := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => (h ha).elim⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.succ_pos k)
      exact ⟨c, fun _ => by rw [hc, inv_mul_cancel₀ ha]⟩
  choose c hc using hc
  let q : ℂ[X] := Lagrange.interpolate f.roots.toFinset id c
  have hq : ∀ a ∈ f.roots, q.eval a = c a := by
    intro a ha
    exact Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id) c
      (Set.injOn_id _) (Multiset.mem_toFinset.mpr ha)
  let g : ℂ[X] := X * q ^ (k + 1) - 1
  have hg : ∀ a ∈ f.roots, g.IsRoot a := by
    intro a ha
    have := hc a (hroot0 a ha)
    simp only [g, IsRoot, eval_sub, eval_mul, eval_X, eval_pow, eval_one, hq a ha]
    rw [mul_comm, this, sub_self]
  have hdvd : f ∣ g ^ f.natDegree := dvd_pow_natDegree_of_forall_isRoot f g hfm hg
  let r : AdjoinRoot f := AdjoinRoot.root f
  let x : AdjoinRoot f := AdjoinRoot.mk f q
  let P : (AdjoinRoot f)[X] := C r * X ^ (k + 1) - 1
  have hPx : ∀ z, aeval z P = r * z ^ (k + 1) - 1 := by intro z; simp [P]
  have hmk : r * x ^ (k + 1) - 1 = AdjoinRoot.mk f g := by
    simp [r, x, g, map_sub, map_mul, map_pow, AdjoinRoot.mk_X]
  have hnil : IsNilpotent (aeval x P) := by
    refine ⟨f.natDegree, ?_⟩
    rw [hPx, hmk, ← map_pow, AdjoinRoot.mk_eq_zero]
    exact hdvd
  have hunit : IsUnit (r * x ^ (k + 1)) := by
    have := hnil.isUnit_add_one
    rwa [hPx, sub_add_cancel] at this
  have hunit' : IsUnit (r * x ^ k) := by
    rw [pow_succ, ← mul_assoc] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have hl : IsUnit ((k + 1 : ℕ) : AdjoinRoot f) := by
    have : IsUnit ((k + 1 : ℕ) : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa using this.map (algebraMap ℂ (AdjoinRoot f))
  have hder : IsUnit (aeval x (derivative P)) := by
    have h1 : aeval x (derivative P) = ((k + 1 : ℕ) : AdjoinRoot f) * (r * x ^ k) := by
      simp [P]
      ring
    rw [h1]
    exact hl.mul hunit'
  obtain ⟨y, ⟨_, hy⟩, _⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hder
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨p, ?_⟩
  have e : (AdjoinRoot.mk f p) ^ (k + 1) * r = 1 := by
    rw [mul_comm]
    rw [hPx] at hy
    exact sub_eq_zero.mp hy
  have e2 : AdjoinRoot.mk f (p ^ (k + 1) * X - 1) = 0 := by
    rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one]
    exact sub_eq_zero.mpr e
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_eq_zero.mp e2
  have h2 := congrArg (aeval B) hb
  rw [map_mul, hB0, zero_mul, map_sub, map_mul, map_pow, aeval_X, map_one] at h2
  exact sub_eq_zero.mp h2

end GlobalTheory
