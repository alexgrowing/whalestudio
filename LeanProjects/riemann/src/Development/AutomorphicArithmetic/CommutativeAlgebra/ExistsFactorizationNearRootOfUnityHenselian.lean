import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsZeroOfLinearFormJacobianHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPowerDecompositionOfRootOfUnity
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartQuotientOfFiniteCoord

noncomputable section
open IsLocalRing UpperTheory.Et

namespace UpperTheory.LinearFiltration

section
variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

private lemma mem_S (T : TC A D) (j : ℕ) (x : D) :
    x ∈ T.S j ↔ x ∈ T.B ∧ T.s ^ j * x ∈ T.C := (Iff.rfl)

private lemma S_mul (T : TC A D) {i j : ℕ} {x y : D} (hx : x ∈ T.S i) (hy : y ∈ T.S j) :
    x * y ∈ T.S (i + j) := by
  rw [mem_S] at *
  refine ⟨T.B.mul_mem hx.1 hy.1, ?_⟩
  have := T.C.mul_mem hx.2 hy.2
  convert this using 1
  ring

private lemma S_one (T : TC A D) (j : ℕ) : (1 : D) ∈ T.S j := by
  rw [mem_S]
  refine ⟨one_mem _, ?_⟩
  rw [mul_one]
  exact pow_mem T.sC j

private lemma S_pow (T : TC A D) {j : ℕ} {x : D} (hx : x ∈ T.S j) (k : ℕ) :
    x ^ k ∈ T.S (k * j) := by
  induction k with
  | zero => simpa using S_one T 0
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact S_mul T ih hx

private lemma st_pow (T : TC A D) (j : ℕ) : T.s ^ j * T.t ^ j = 1 := by
  rw [← mul_pow, mul_comm, T.ts, one_pow]

private lemma power_mem_filtration (T : TC A D) (j : ℕ) : T.t ^ j ∈ T.S j := by
  rw [mem_S]
  refine ⟨pow_mem T.tB j, ?_⟩
  rw [st_pow]
  exact one_mem _

private lemma coord_setup (T : TC A D) (hC : T.Coord) (j : ℕ) :
    ∃ (n : ℕ) (e : Fin n → D) (L : D →ₗ[A] (Fin n → A)),
      (∀ i, e i ∈ T.S j) ∧ (∀ i k, L (e k) i = if i = k then 1 else 0) ∧
        ∀ x ∈ T.S j, L x = 0 → x = 0 := by
  classical
  obtain ⟨ι, β, U, V, hB, hV⟩ := hC
  obtain ⟨hVj, hfin⟩ := hV j
  set F := hfin.toFinset with hF
  have hSB : ∀ x, x ∈ T.B ↔ ↑(β.repr x).support ⊆ U := by
    intro x
    rw [← Subalgebra.mem_toSubmodule, hB, Module.Basis.mem_span_image]
  have hSC : ∀ x, T.s ^ j * x ∈ T.C ↔ ↑(β.repr x).support ⊆ V j := by
    intro x
    change x ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C) ↔ _
    rw [hVj, Module.Basis.mem_span_image]
  let L : D →ₗ[A] (Fin F.card → A) :=
    LinearMap.pi fun i => (Finsupp.lapply (F.equivFin.symm i : ι)).comp β.repr.toLinearMap
  refine ⟨F.card, fun i => β (F.equivFin.symm i : ι), L, ?_, ?_, ?_⟩
  · intro i
    have hi : (F.equivFin.symm i : ι) ∈ U ∩ V j := hfin.mem_toFinset.1 (F.equivFin.symm i).2
    rw [mem_S, hSB, hSC, Module.Basis.repr_self]
    refine ⟨?_, ?_⟩ <;> refine (Finset.coe_subset.2 Finsupp.support_single_subset).trans ?_ <;>
      simp [hi.1, hi.2]
  · intro i k
    change β.repr (β (F.equivFin.symm k : ι)) (F.equivFin.symm i : ι) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro h'
      exact h (F.equivFin.symm.injective (Subtype.ext h'.symm))
  · intro x hx hL
    rw [mem_S, hSB, hSC] at hx
    have h0 : β.repr x = 0 := by
      ext a
      by_cases ha : a ∈ (β.repr x).support
      · have haF : a ∈ F := hfin.mem_toFinset.2 ⟨hx.1 ha, hx.2 ha⟩
        have h1 := congrFun hL (F.equivFin ⟨a, haF⟩)
        change β.repr x (F.equivFin.symm (F.equivFin ⟨a, haF⟩) : ι) = 0 at h1
        simpa using h1
      · simpa using ha
    simpa using h0

private lemma L_mem {n : ℕ} (I : Ideal A) (L : D →ₗ[A] (Fin n → A)) (x : D)
    (hx : x ∈ I.map (algebraMap A D)) (i : Fin n) : L x i ∈ I := by
  have key : ∀ d : D, ∀ i, L (d * x) i ∈ I := by
    change x ∈ Submodule.span D (algebraMap A D '' (I : Set A)) at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro d i
      rw [mul_comm, ← Algebra.smul_def, map_smul]
      simpa using I.mul_mem_right (L d i) ha
    | zero => intro d i; simp
    | add y z _ _ hy hz =>
      intro d i
      rw [mul_add, map_add]
      exact I.add_mem (hy d i) (hz d i)
    | smul e y _ hy =>
      intro d i
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (d * e) i
  simpa using key 1 i

end

section
variable {D : Type} [CommRing D] {n : ℕ}

private def lin (c : D) (a : Fin n → D) : MvPolynomial (Fin n) D :=
  MvPolynomial.C c + ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

private lemma eval_lin (c : D) (a y : Fin n → D) :
    MvPolynomial.eval y (lin c a) = c + ∑ i, a i * y i := by
  simp [lin]

private lemma pderiv_lin (c : D) (a : Fin n → D) (j : Fin n) :
    MvPolynomial.pderiv j (lin c a) = MvPolynomial.C (a j) := by
  simp [lin, MvPolynomial.pderiv_X, Pi.single_apply, map_sum, Derivation.leibniz]

end

private lemma mem_mm_top {A D : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (x : D) :
    x ∈ mm (⊤ : Subalgebra A D) ↔ x ∈ (maximalIdeal A).map (algebraMap A D) := by
  change x ∈ maximalIdeal A • (⊤ : Submodule A D) ↔ _
  rw [Ideal.smul_top_eq_map]
  rfl

end UpperTheory.LinearFiltration

open UpperTheory.LinearFiltration in
theorem UpperTheory.exists_factorization_near_root_of_unity_henselian :
    ∀ (A D : Type) [CommRing A] [HenselianLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ (q : ℕ), IsUnit (q : A) → ∀ ω : D, ω ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ g' ∈ T.B, ∃ g ∈ T.C, ∃ μ : D, g' - 1 ∈ mm T.B ∧ g - 1 ∈ mm T.C ∧ μ - ω ∈ mm (⊤ : Subalgebra A D) ∧ g * g' = μ ^ q := by
  intro A D _ _ _ _ T hF hC q hq ω hω
  classical
  set M := maximalIdeal A with hM
  set J := M.map (algebraMap A D) with hJ
  have hωJ : ω ^ q - 1 ∈ J := (mem_mm_top _).1 hω
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  obtain ⟨T', hT'F, hT't, -, hlift, hproj, -, -⟩ := exists_twoChart_quotient_of_finite_coord A D T hF hC M
  have hω' : (Ideal.Quotient.mk J ω) ^ q = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact hωJ
  obtain ⟨m₀, hm₀⟩ := exists_power_decomposition_of_root_of_unity A (D ⧸ J) T' hT'F q hq hq0 (Ideal.Quotient.mk J ω) hω'
  obtain ⟨k₁, hk₁⟩ := T.locB ω
  obtain ⟨k₂, hk₂⟩ := T.locC ω
  obtain ⟨m, hm⟩ : ∃ m, m = m₀ + k₁ + k₂ := ⟨_, rfl⟩
  have hmm : m ≥ m₀ := by omega
  have hW : ω * T.t ^ m ∈ T.S (2 * m) := by
    rw [mem_S]
    constructor
    · have e : ω * T.t ^ m = T.t ^ (m₀ + k₂) * (T.t ^ k₁ * ω) := by rw [hm]; ring
      rw [e]
      exact mul_mem (pow_mem T.tB _) hk₁
    · have e : T.s ^ (2 * m) * (ω * T.t ^ m) = T.s ^ (m₀ + k₁) * (T.s ^ k₂ * ω) := by
        calc T.s ^ (2 * m) * (ω * T.t ^ m) = T.s ^ m * (T.s ^ m * T.t ^ m) * ω := by ring
          _ = T.s ^ m * ω := by rw [st_pow]; ring
          _ = _ := by rw [hm]; ring
      rw [e]
      exact mul_mem (pow_mem T.sC _) hk₂
  obtain ⟨n, e, L, he, hLe, hLinj⟩ := coord_setup T hC (2 * q * m)
  have hdec : ∀ k, ∃ a ∈ T.S (q * m), ∃ b ∈ T.S (q * m), ∃ c ∈ T.S (2 * m),
      a + T.t ^ (q * m) * b - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c - e k ∈ J := by
    intro k
    obtain ⟨a', ha', b', hb', c', hc', hk⟩ := (hm₀ m hmm).2 _ (hproj _ _ (he k))
    obtain ⟨a, ha, rfl⟩ := hlift _ _ ha'
    obtain ⟨b, hb, rfl⟩ := hlift _ _ hb'
    obtain ⟨c, hc, rfl⟩ := hlift _ _ hc'
    refine ⟨a, ha, b, hb, c, hc, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [hT't] at hk
    simp only [map_sub, map_add, map_mul, map_pow, map_natCast]
    rw [hk]
    ring
  choose a ha b hb c hc hkey using hdec
  set Φ : MvPolynomial (Fin n) D :=
    lin (T.t ^ (q * m)) a * lin 1 b - (lin (ω * T.t ^ m) c) ^ q with hΦ
  have ev0 : ∀ (c0 : D) (v : Fin n → D), MvPolynomial.eval 0 (lin c0 v) = c0 := by
    intro c0 v
    rw [eval_lin]
    simp
  have h0 : ∀ i, L (MvPolynomial.eval 0 Φ) i ∈ M := by
    intro i
    apply L_mem M L
    have e0 : MvPolynomial.eval 0 Φ = -(T.t ^ (q * m)) * (ω ^ q - 1) := by
      rw [hΦ]
      simp only [map_sub, map_mul, map_pow, ev0]
      ring
    rw [e0]
    exact J.mul_mem_left _ hωJ
  have hd0 : ∀ j, MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ) =
      a j + T.t ^ (q * m) * b j - (q : D) * (ω * T.t ^ m) ^ (q - 1) * c j := by
    intro j
    rw [hΦ]
    simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, pderiv_lin, smul_eq_mul,
      nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast, ev0, MvPolynomial.eval_C]
    ring
  have hd : ∀ i j, L (MvPolynomial.eval 0 (MvPolynomial.pderiv j Φ)) i - (if i = j then 1 else 0) ∈ M := by
    intro i j
    have h1 := L_mem M L _ (hkey j) i
    rw [map_sub, Pi.sub_apply, hLe i j] at h1
    rw [hd0]
    exact h1
  obtain ⟨x, hxM, hΦx⟩ := exists_zero_of_linear_form_jacobian_henselian A D n Φ L h0 hd
  set y : Fin n → D := fun j => algebraMap A D (x j) with hy
  have hsum : ∀ (j : ℕ) (v : Fin n → D), (∀ k, v k ∈ T.S j) → ∑ k, v k * y k ∈ T.S j := by
    intro j v hv
    refine Submodule.sum_mem _ (fun k _ => ?_)
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hv k)
  have hsumM : ∀ (S : Subalgebra A D) (v : Fin n → D), (∀ k, v k ∈ S) → ∑ k, v k * y k ∈ mm S := by
    intro S v hv
    refine Submodule.sum_mem _ (fun k _ => ?_)
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (hxM k) (by simpa using hv k)
  have hev : MvPolynomial.eval y Φ = (T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k) -
      (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by
    rw [hΦ]
    simp only [map_sub, map_mul, map_pow, eval_lin]
  have hmem : MvPolynomial.eval y Φ ∈ T.S (2 * q * m) := by
    rw [hev]
    refine Submodule.sub_mem _ ?_ ?_
    · have e1 : 2 * q * m = q * m + q * m := by ring
      rw [e1]
      exact S_mul T (Submodule.add_mem _ (power_mem_filtration T _) (hsum _ _ ha))
        (Submodule.add_mem _ (S_one T _) (hsum _ _ hb))
    · have e2 : 2 * q * m = q * (2 * m) := by ring
      rw [e2]
      exact S_pow T (Submodule.add_mem _ hW (hsum _ _ hc)) q
  have hzero := hLinj _ hmem hΦx
  have hkey2 : (T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k) =
      (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by
    rw [hev] at hzero
    exact sub_eq_zero.1 hzero
  refine ⟨1 + ∑ k, b k * y k, ?_, 1 + T.s ^ (q * m) * ∑ k, a k * y k, ?_,
    ω + T.s ^ m * ∑ k, c k * y k, ?_, ?_, ?_, ?_⟩
  · exact add_mem (one_mem _) ((mem_S T _ _).1 (hsum _ _ hb)).1
  · exact add_mem (one_mem _) ((mem_S T _ _).1 (hsum _ _ ha)).2
  · rw [add_sub_cancel_left]
    exact hsumM T.B b (fun k => ((mem_S T _ _).1 (hb k)).1)
  · rw [add_sub_cancel_left, Finset.mul_sum]
    simp_rw [← mul_assoc]
    exact hsumM T.C (fun k => T.s ^ (q * m) * a k) (fun k => ((mem_S T _ _).1 (ha k)).2)
  · rw [add_sub_cancel_left, Finset.mul_sum]
    simp_rw [← mul_assoc]
    exact hsumM ⊤ (fun k => T.s ^ m * c k) (fun _ => Algebra.mem_top)
  · calc (1 + T.s ^ (q * m) * ∑ k, a k * y k) * (1 + ∑ k, b k * y k)
          = T.s ^ (q * m) * ((T.t ^ (q * m) + ∑ k, a k * y k) * (1 + ∑ k, b k * y k)) := by
            have h := st_pow T (q * m)
            linear_combination (-(1 + ∑ k, b k * y k)) * h
      _ = T.s ^ (q * m) * (ω * T.t ^ m + ∑ k, c k * y k) ^ q := by rw [hkey2]
      _ = (ω + T.s ^ m * ∑ k, c k * y k) ^ q := by
            rw [show T.s ^ (q * m) = (T.s ^ m) ^ q by ring, ← mul_pow]
            congr 1
            linear_combination ω * st_pow T m

end
