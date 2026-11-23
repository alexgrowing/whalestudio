import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSerreGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace SerreGraded

open Polynomial

section Pieces

variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)

theorem mul_mem_succ (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) :
    x * w j ∈ gradedSpan w d t (k + 1) := by
  classical
  have hle : gradedSpan w d t k ≤
      (gradedSpan w d t (k + 1)).comap (AddMonoidHom.mulRight (w j)) := by
    rw [gradedSpan, AddSubgroup.closure_le]
    rintro _ ⟨l, μ, hμ, rfl⟩
    refine AddSubgroup.subset_closure ⟨l, μ + Pi.single j 1, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, ← hμ, add_assoc]
    · have h1 : ∏ i, w i ^ (μ + Pi.single j 1 : Fin q → ℕ) i =
          (∏ i, w i ^ μ i) * ∏ i, w i ^ (Pi.single j 1 : Fin q → ℕ) i := by
        rw [← Finset.prod_mul_distrib]; simp [pow_add]
      have h2 : ∏ i, w i ^ (Pi.single j 1 : Fin q → ℕ) i = w j := by
        rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp
      rw [h1, h2]; simp [mul_assoc]
  exact hle hx

theorem mul_pow_mem (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) (e : ℕ) :
    x * w j ^ e ∈ gradedSpan w d t (k + e) := by
  induction e with
  | zero => simpa using hx
  | succ e ih =>
    have h := mul_mem_succ w d t j ih
    rw [pow_succ, ← mul_assoc]
    exact h

end Pieces

section Action

variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)

def act : MvPolynomial (Fin q) ℤ →+* (Polynomial Ω) :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial Ω)) (fun j => C (w j) * X)

theorem act_X (j : Fin q) : act w (MvPolynomial.X j) = C (w j) * X := by
  simp [act]

theorem act_monomial (v : Fin q →₀ ℕ) (a : ℤ) :
    act w (MvPolynomial.monomial v a) = C ((a : Ω) * ∏ j, w j ^ v j) * X ^ (∑ j, v j) := by
  rw [act, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

theorem act_prod_X_pow (μ : Fin q → ℕ) :
    act w (∏ j, MvPolynomial.X j ^ μ j) = C (∏ j, w j ^ μ j) * X ^ (∑ j, μ j) := by
  simp [map_prod, act_X, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Action

def gradedModule (q : ℕ) {Ω : Type} [Field Ω] {r : ℕ} [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
    (d : Fin r → ℕ) (t : Fin r → Ω) : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
  Submodule.span _ (Set.range fun l => C (t l) * X ^ d l)

section Module

variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]

def shifted (u : Fin q) : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
  (gradedModule q d t).map (LinearMap.mulLeft _ (C (w u) * X))

theorem smul_eq (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (c : MvPolynomial (Fin q) ℤ)
    (p : (Polynomial Ω)) : c • p = act w c * p := by
  rw [Algebra.smul_def, hA]

theorem smul_coeff_mem (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w)
    (c : MvPolynomial (Fin q) ℤ) {p : (Polynomial Ω)} (hp : ∀ n, p.coeff n ∈ gradedSpan w d t n) :
    ∀ n, (c • p).coeff n ∈ gradedSpan w d t n := by
  induction c using MvPolynomial.induction_on generalizing p with
  | C a =>
    intro n
    rw [smul_eq w hA, act, MvPolynomial.eval₂Hom_C, eq_intCast, ← C_eq_intCast, coeff_C_mul,
      ← zsmul_eq_mul]
    exact zsmul_mem (hp n) a
  | add a b ha hb =>
    intro n
    rw [add_smul, coeff_add]
    exact add_mem (ha hp n) (hb hp n)
  | mul_X a j ha =>
    rw [mul_smul]
    apply ha
    intro n
    rw [smul_eq w hA, act_X]
    cases n with
    | zero => simp [mul_assoc]
    | succ k =>
      rw [mul_assoc, coeff_C_mul, coeff_X_mul, mul_comm]
      exact mul_mem_succ w d t j (hp k)

theorem coeff_mem (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) {m : (Polynomial Ω)}
    (hm : m ∈ gradedModule q d t) (n : ℕ) : m.coeff n ∈ gradedSpan w d t n := by
  let P : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
    { carrier := {p | ∀ n, p.coeff n ∈ gradedSpan w d t n}
      add_mem' := fun ha hb n => by rw [coeff_add]; exact add_mem (ha n) (hb n)
      zero_mem' := fun n => by simp
      smul_mem' := fun c _ hp => smul_coeff_mem w d t hA c hp }
  have hle : gradedModule q d t ≤ P := by
    rw [gradedModule, Submodule.span_le]
    rintro _ ⟨l, rfl⟩ n
    rw [coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      simpa using gradedSpan_gen_mem w d t l 0
    · exact zero_mem _
  exact hle hm n

theorem monomial_mem (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) {n : ℕ} {x : Ω}
    (hx : x ∈ gradedSpan w d t n) : C x * X ^ n ∈ gradedModule q d t := by
  have hle : gradedSpan w d t n ≤ ((gradedModule q d t).toAddSubgroup).comap
      ((Polynomial.monomial n : Ω →ₗ[Ω] (Polynomial Ω)).toAddMonoidHom) := by
    rw [gradedSpan, AddSubgroup.closure_le]
    rintro _ ⟨l, μ, hμ, rfl⟩
    change (Polynomial.monomial n) (t l * ∏ j, w j ^ μ j) ∈ gradedModule q d t
    have heq : (∏ j, MvPolynomial.X j ^ μ j : MvPolynomial (Fin q) ℤ) • (C (t l) * X ^ d l) =
        Polynomial.monomial n (t l * ∏ j, w j ^ μ j) := by
      rw [smul_eq w hA, act_prod_X_pow, ← C_mul_X_pow_eq_monomial, ← hμ, C_mul, pow_add]
      ring
    rw [← heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have := hle hx
  simpa [C_mul_X_pow_eq_monomial] using this

theorem coeff_shifted (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) {y : (Polynomial Ω)}
    (hy : y ∈ shifted w d t u) (k : ℕ) : ∃ z ∈ gradedSpan w d t k, y.coeff (k + 1) = w u * z := by
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨m.coeff k, coeff_mem w d t hA hm k, ?_⟩
  rw [LinearMap.mulLeft_apply, mul_assoc, coeff_C_mul, coeff_X_mul]

end Module

section Torsion

variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]

theorem exists_common {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ D, ∀ D', D ≤ D' → P i D') : ∃ D, ∀ i ∈ s, P i D := by
  classical
  choose! f hf using h
  exact ⟨s.sup f, fun i hi => hf i hi _ (Finset.le_sup hi)⟩

theorem torsion_bound (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) :
    ∃ E : ℕ, ∀ m ∈ gradedModule q d t,
      (∀ j, w j ≠ 0 → ∃ D : ℕ,
        (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • m ∈ shifted w d t u) →
      ∀ k, E ≤ k → ∃ z ∈ gradedSpan w d t k, m.coeff (k + 1) = w u * z := by
  classical
  set N := shifted w d t u with hN
  have hpow : ∀ (j : Fin q) (g : Polynomial Ω) (D : ℕ),
      (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • g ∈ N → ∀ D', D ≤ D' →
      (MvPolynomial.X j ^ D' : MvPolynomial (Fin q) ℤ) • g ∈ N := by
    intro j g D h D' hD'
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hD'
    rw [pow_add, mul_comm, mul_smul]
    exact N.smul_mem _ h
  let Γ : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
    { carrier := {m | m ∈ gradedModule q d t ∧
        ∀ j, w j ≠ 0 → ∃ D : ℕ, (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) • m ∈ N}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun j hj => ?_⟩
        obtain ⟨D₁, h₁⟩ := ha' j hj
        obtain ⟨D₂, h₂⟩ := hb' j hj
        refine ⟨D₁ + D₂, ?_⟩
        rw [smul_add]
        exact add_mem (hpow j a D₁ h₁ _ (by omega)) (hpow j b D₂ h₂ _ (by omega))
      zero_mem' := ⟨zero_mem _, fun j _ => ⟨0, by simp⟩⟩
      smul_mem' := by
        rintro c m ⟨hm, hm'⟩
        refine ⟨Submodule.smul_mem _ c hm, fun j hj => ?_⟩
        obtain ⟨D, hD⟩ := hm' j hj
        refine ⟨D, ?_⟩
        rw [← mul_smul, mul_comm, mul_smul]
        exact N.smul_mem c hD }
  have hMfg : (gradedModule q d t).FG := by
    refine ⟨Finset.univ.image (fun l => C (t l) * X ^ d l), ?_⟩
    rw [gradedModule, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hNoeth : IsNoetherian (MvPolynomial (Fin q) ℤ) (gradedModule q d t) :=
    isNoetherian_of_fg_of_noetherian _ hMfg
  obtain ⟨S, hS⟩ : Γ.FG := isNoetherian_submodule.mp hNoeth Γ (fun m hm => hm.1)
  have hgen : ∀ g ∈ S, g ∈ Γ := fun g hg => by
    rw [← hS]; exact Submodule.subset_span (by exact_mod_cast hg)
  obtain ⟨Dm, hDm⟩ := exists_common (S ×ˢ (Finset.univ : Finset (Fin q)))
    (fun p D => (MvPolynomial.X p.2 ^ D : MvPolynomial (Fin q) ℤ) • p.1 ∈ N) (by
      rintro ⟨g, j⟩ hgj
      rw [Finset.mem_product] at hgj
      by_cases hj : w j = 0
      · refine ⟨1, fun D' hD' => hpow j g 1 ?_ D' hD'⟩
        rw [pow_one, smul_eq w hA, act_X, hj, map_zero, zero_mul, zero_mul]
        exact zero_mem _
      · obtain ⟨D, hD⟩ := (hgen g hgj.1).2 j hj
        exact ⟨D, hpow j g D hD⟩)
  refine ⟨q * Dm + S.sup natDegree, fun m hm htors k hk => ?_⟩
  have hmΓ : m ∈ Γ := ⟨hm, htors⟩
  rw [← hS, Submodule.mem_span_finset] at hmΓ
  obtain ⟨f, -, rfl⟩ := hmΓ
  suffices hT : (∑ g ∈ S, f g • g).coeff (k + 1) ∈
      (gradedSpan w d t k).map (AddMonoidHom.mulLeft (w u)) by
    obtain ⟨z, hz, hz'⟩ := AddSubgroup.mem_map.mp hT
    exact ⟨z, hz, hz'.symm⟩
  rw [finsetSum_coeff]
  refine AddSubgroup.sum_mem _ fun g hg => ?_
  rw [MvPolynomial.as_sum (f g), Finset.sum_smul, finsetSum_coeff]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  by_cases hlow : ∀ j, v j < Dm
  · have hdeg : (MvPolynomial.monomial v (MvPolynomial.coeff v (f g)) • g).natDegree < k + 1 := by
      rw [smul_eq w hA, act_monomial]
      have h1 := natDegree_mul_le (p := C (((MvPolynomial.coeff v (f g) : ℤ) : Ω) * ∏ j, w j ^ v j) *
        X ^ (∑ j, v j)) (q := g)
      have h2 := natDegree_C_mul_X_pow_le (((MvPolynomial.coeff v (f g) : ℤ) : Ω) * ∏ j, w j ^ v j)
        (∑ j, v j)
      have h3 : ∑ j, v j ≤ q * Dm := by
        calc ∑ j, v j ≤ ∑ _j : Fin q, Dm := Finset.sum_le_sum fun j _ => (hlow j).le
          _ = q * Dm := by simp
      have h4 : g.natDegree ≤ S.sup natDegree := Finset.le_sup (f := natDegree) hg
      omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg]
    exact zero_mem _
  · simp only [not_forall, not_lt] at hlow
    obtain ⟨j, hj⟩ := hlow
    have hsplit : MvPolynomial.monomial v (MvPolynomial.coeff v (f g)) =
        MvPolynomial.monomial (v - Finsupp.single j Dm) (MvPolynomial.coeff v (f g)) *
          MvPolynomial.X j ^ Dm := by
      rw [← MvPolynomial.monomial_add_single, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)]
    rw [hsplit, mul_smul]
    obtain ⟨z, hz, hz'⟩ := coeff_shifted w d t hA u
      (N.smul_mem _ (hDm (g, j) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ j⟩))) k
    rw [hz']
    exact AddSubgroup.mem_map.mpr ⟨z, hz, rfl⟩

end Torsion

theorem proof : SerreGraded.Statement := by
  intro Ω _ q r w d t ⟨u, hu⟩
  classical
  let _ : Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω) := (act w).toAlgebra
  have hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w := rfl
  obtain ⟨E, hE⟩ := torsion_bound w d t hA u
  refine ⟨E, fun n hn s hs => ?_⟩
  have step : ∀ k, s * w u ^ (k + 1) ∈ gradedSpan w d t (n + k + 1) →
      s * w u ^ k ∈ gradedSpan w d t (n + k) := by
    intro k hk
    have hm := monomial_mem w d t hA hk
    have htors : ∀ j, w j ≠ 0 → ∃ D : ℕ, (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) •
        (C (s * w u ^ (k + 1)) * X ^ (n + k + 1)) ∈ shifted w d t u := by
      intro j hj
      obtain ⟨D, hD⟩ := hs j hj
      refine ⟨D, Submodule.mem_map.mpr ⟨C (s * w j ^ D * w u ^ k) * X ^ (n + D + k),
        monomial_mem w d t hA (mul_pow_mem w d t u hD k), ?_⟩⟩
      rw [LinearMap.mulLeft_apply, smul_eq w hA, map_pow, act_X]
      simp only [C_mul, C_pow]
      ring
    obtain ⟨z, hz, hz'⟩ := hE _ hm htors (n + k) (by omega)
    rw [coeff_C_mul_X_pow, if_pos rfl] at hz'
    have hcancel : w u * (s * w u ^ k) = w u * z := by rw [← hz']; ring
    rw [mul_left_cancel₀ hu hcancel]
    exact hz
  have desc : ∀ D, s * w u ^ D ∈ gradedSpan w d t (n + D) → s ∈ gradedSpan w d t n := by
    intro D
    induction D with
    | zero => intro h; simpa using h
    | succ D ih => exact fun h => ih (step D h)
  obtain ⟨D, hD⟩ := hs u hu
  exact desc D hD

end SerreGraded

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
