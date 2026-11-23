import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd.DCoset

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem le_ofAdd_neg_one_of_lt_one {y : WithZero (Multiplicative ℤ)} (h : y < 1) :
    y ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem exists_residue_reps {q : ℕ} (hq : 2 ≤ q)
    (hcard : Nat.card ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer ⧸
      IsLocalRing.maximalIdeal (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2) :
    ∃ R : Set K, R.Finite ∧ R ⊆ intL K ∧ ∀ x ∈ intL K, ∃ r ∈ R,
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (x - r) < 1 := by
  set v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
  have hfin : Finite (v.integer ⧸ IsLocalRing.maximalIdeal v.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI : Finite (v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring) := hfin
  let f : v.valuationSubring ⧸ IsLocalRing.maximalIdeal v.valuationSubring → K :=
    fun c => ((Ideal.Quotient.mk_surjective c).choose : K)
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    show _ ∈ v.integer
    rw [Valuation.mem_integer_iff]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (Ideal.Quotient.mk_surjective c).choose.2
  · intro x hx
    have hx' : x ∈ v.valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ((Valuation.mem_integer_iff _ _).1 hx)
    let xs : v.valuationSubring := ⟨x, hx'⟩
    let c := Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring) xs
    refine ⟨f c, ⟨c, rfl⟩, ?_⟩
    have hspec := (Ideal.Quotient.mk_surjective c).choose_spec
    have hmem : xs - (Ideal.Quotient.mk_surjective c).choose ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
      Ideal.Quotient.eq.1 (hspec.symm)
    rw [ValuationSubring.valuation_lt_one_iff] at hmem
    have := (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one.2 hmem
    simpa [xs, f] using this

end GlobalTheory.SatInd.DCoset

namespace GlobalTheory.SatInd.DCoset

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_trunc (ϖ : K)
    (hϖ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {R : Set K} (hRf : R.Finite) (hRO : R ⊆ intL K)
    (hR : ∀ x ∈ intL K, ∃ r ∈ R, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (x - r) < 1) :
    ∀ N : ℕ, ∃ T : Set K, T.Finite ∧ T ⊆ intL K ∧ ∀ x ∈ intL K, ∃ t ∈ T,
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (x - t) ≤
        (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ϖ ^ N := by
  set v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hϖ1 : v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    norm_num
  have hϖO : ϖ ∈ intL K := (Valuation.mem_integer_iff _ _).2 hϖ1
  intro N
  induction N with
  | zero =>
    refine ⟨{0}, Set.finite_singleton 0, ?_, ?_⟩
    · rintro _ rfl; exact (intL K).zero_mem
    · intro x hx
      refine ⟨0, rfl, ?_⟩
      rw [sub_zero, pow_zero]
      exact (Valuation.mem_integer_iff _ _).1 hx
  | succ N ih =>
    obtain ⟨T, hTf, hTO, hT⟩ := ih
    refine ⟨Set.image2 (fun r t => r + ϖ * t) R T, hRf.image2 _ hTf, ?_, ?_⟩
    · rintro _ ⟨r, hr, t, ht, rfl⟩
      exact (intL K).add_mem (hRO hr) ((intL K).mul_mem hϖO (hTO ht))
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := hR x hx
      have hle : v (x - r) ≤ v ϖ := hϖ ▸ le_ofAdd_neg_one_of_lt_one hxr
      set y := (x - r) * ϖ⁻¹ with hy
      have hyO : y ∈ intL K := by
        apply (Valuation.mem_integer_iff _ _).2
        rw [hy, map_mul, map_inv₀]
        calc v (x - r) * (v ϖ)⁻¹ ≤ v ϖ * (v ϖ)⁻¹ := mul_le_mul' hle le_rfl
          _ = 1 := mul_inv_cancel₀ h0
      obtain ⟨t, ht, hyt⟩ := hT y hyO
      refine ⟨r + ϖ * t, ⟨r, hr, t, ht, rfl⟩, ?_⟩
      have he : x - (r + ϖ * t) = ϖ * (y - t) := by
        rw [hy]; field_simp; ring
      rw [he, map_mul, pow_succ']
      exact mul_le_mul' le_rfl hyt

theorem exists_le_inv_pow (ϖ : K)
    (hϖ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : K) :
    ∃ M : ℕ, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x ≤
      ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ϖ)⁻¹ ^ M := by
  rw [hϖ]
  generalize (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x = y
  induction y using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe c =>
    refine ⟨(Multiplicative.toAdd c).toNat, ?_⟩
    rw [← WithZero.coe_inv, ← WithZero.coe_pow, WithZero.coe_le_coe]
    show Multiplicative.toAdd c ≤ Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ ^ (Multiplicative.toAdd c).toNat)
    rw [toAdd_pow, toAdd_inv, toAdd_ofAdd]
    simp only [neg_neg, nsmul_eq_mul, mul_one]
    exact Int.self_le_toNat _

end GlobalTheory.SatInd.DCoset

namespace GlobalTheory.SatInd.DCoset

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem entry_mul_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} {α β : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (A i j) ≤ α)
    (hB : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (B i j) ≤ β) :
    ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ((A * B) i j) ≤ α * β := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ (fun k _ => by rw [map_mul]; exact mul_le_mul' (hA i k) (hB k j))

theorem entry_le_one_of_mem_KU {σ : K →+* K} {n : ℕ} {a : GU σ n} (ha : a ∈ KU σ n) (i j : Fin n) :
    (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at ha
  obtain ⟨g, hg⟩ := ha.2
  have h : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      ((g : Matrix (Fin n) (Fin n) (intL K)) i j : K) := by rw [← hg]; rfl
  rw [h]
  exact (Valuation.mem_integer_iff _ _).1 (((g : Matrix (Fin n) (Fin n) (intL K)) i j).2)

theorem mem_KU_of_entries {σ : K →+* K} {n : ℕ} (g : GU σ n)
    (h1 : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (h2 : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      ((((g⁻¹ : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1) :
    g ∈ KU σ n := by
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  let A : Matrix (Fin n) (Fin n) (intL K) := fun i j => ⟨_, (Valuation.mem_integer_iff _ _).2 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (intL K) := fun i j => ⟨_, (Valuation.mem_integer_iff _ _).2 (h2 i j)⟩
  have hA : A.map (intL K).subtype = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext; rfl
  have hB : B.map (intL K).subtype = (((g⁻¹ : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext; rfl
  have hAB : A * B = 1 := by
    apply Matrix.map_injective Subtype.val_injective
    show (A * B).map (intL K).subtype = (1 : Matrix (Fin n) (Fin n) (intL K)).map (intL K).subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv (g : GL (Fin n) K)
  have hBA : B * A = 1 := by
    apply Matrix.map_injective Subtype.val_injective
    show (B * A).map (intL K).subtype = (1 : Matrix (Fin n) (Fin n) (intL K)).map (intL K).subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul (g : GL (Fin n) K)
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

end GlobalTheory.SatInd.DCoset

namespace GlobalTheory.SatInd.DCoset

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem conj_entry_le_one {n : ℕ} {S Si A A' Ai' : Matrix (Fin n) (Fin n) K}
    {C ε : WithZero (Multiplicative ℤ)} (hSi : Si * S = 1) (hA' : Ai' * A' = 1)
    (hS : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (S i j) ≤ C)
    (hSi' : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (Si i j) ≤ C)
    (hAi : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (Ai' i j) ≤ 1)
    (hD : ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (A i j - A' i j) ≤ ε)
    (hCε : C * 1 * ε * C ≤ 1) :
    ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ((Si * Ai' * A * S) i j) ≤ 1 := by
  have e : Si * Ai' * A * S = 1 + Si * Ai' * (A - A') * S := by
    have h1 : Si * Ai' * A' * S = 1 := by rw [Matrix.mul_assoc Si, hA', Matrix.mul_one, hSi]
    rw [Matrix.mul_sub, Matrix.sub_mul, h1]
    abel
  have hX := entry_mul_le (entry_mul_le (entry_mul_le hSi' hAi)
    (show ∀ i j, (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) ((A - A') i j) ≤ ε from
      fun i j => by rw [Matrix.sub_apply]; exact hD i j)) hS
  intro i j
  rw [e, Matrix.add_apply]
  refine Valuation.map_add_le _ ?_ ((hX i j).trans hCε)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem finite_dcoset : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), IsUnramInv ϖ σ q → ∀ s : GU σ n,
      Set.Finite {c : GU σ n ⧸ KU σ n | ∃ a ∈ KU σ n, ((a * s : GU σ n) : GU σ n ⧸ KU σ n) = c} := by
  intro K _ _ ϖ σ q n hU s
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := hU
  obtain ⟨R, hRf, hRO, hR⟩ := exists_residue_reps hq hcard
  set v := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) with hv
  have h0 : v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.coe_ne_zero
  let mat : GU σ n → Matrix (Fin n) (Fin n) K := fun g => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hx := exists_le_inv_pow ϖ hϖ
  set C := (v ϖ)⁻¹ with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (0 : ℤ) ≤ Multiplicative.toAdd (Multiplicative.ofAdd (-1 : ℤ))⁻¹
    simp
  let f : Fin n × Fin n → ℕ := fun p => (hx (mat s p.1 p.2)).choose + (hx (mat s⁻¹ p.1 p.2)).choose
  set M := Finset.univ.sup f with hM
  have hfM : ∀ i j, f (i, j) ≤ M := fun i j => Finset.le_sup (f := f) (Finset.mem_univ (i, j))
  have hs : ∀ i j, v (mat s i j) ≤ C ^ M := fun i j =>
    (hx (mat s i j)).choose_spec.trans
      (pow_le_pow_right' hC1 ((Nat.le_add_right _ _).trans (hfM i j)))
  have hsi : ∀ i j, v (mat s⁻¹ i j) ≤ C ^ M := fun i j =>
    (hx (mat s⁻¹ i j)).choose_spec.trans
      (pow_le_pow_right' hC1 ((Nat.le_add_left _ _).trans (hfM i j)))
  obtain ⟨T, hTf, hTO, hT⟩ := exists_trunc ϖ hϖ hRf hRO hR (M + M)
  have hCε : C ^ M * 1 * (v ϖ) ^ (M + M) * C ^ M ≤ 1 := by
    apply le_of_eq
    calc C ^ M * 1 * (v ϖ) ^ (M + M) * C ^ M = (C * v ϖ) ^ M * (v ϖ * C) ^ M := by
          rw [mul_one, pow_add, ← mul_assoc, mul_assoc (C ^ M * v ϖ ^ M), mul_pow, mul_pow]
      _ = 1 := by rw [hCdef, inv_mul_cancel₀ h0, mul_inv_cancel₀ h0, one_pow, one_mul]
  have hent : ∀ a : KU σ n, ∀ i j, mat (a : GU σ n) i j ∈ intL K := fun a i j =>
    (Valuation.mem_integer_iff _ _).2 (entry_le_one_of_mem_KU a.2 i j)
  let F : KU σ n → (Fin n → Fin n → T) := fun a i j =>
    ⟨(hT _ (hent a i j)).choose, (hT _ (hent a i j)).choose_spec.1⟩
  have hF : ∀ (a : KU σ n) i j, v (mat (a : GU σ n) i j - (F a i j : K)) ≤ v ϖ ^ (M + M) := fun a i j =>
    (hT _ (hent a i j)).choose_spec.2
  have half : ∀ a a' : KU σ n, F a = F a' → ∀ i j,
      v ((mat s⁻¹ * mat ((a' : GU σ n)⁻¹) * mat (a : GU σ n) * mat s) i j) ≤ 1 := by
    intro a a' haa'
    refine conj_entry_le_one (Units.inv_mul (s : GL (Fin n) K))
      (Units.inv_mul ((a' : GU σ n) : GL (Fin n) K)) hs hsi
      (entry_le_one_of_mem_KU (inv_mem a'.2)) (fun i j => ?_) hCε
    have e : mat (a : GU σ n) i j - mat (a' : GU σ n) i j =
        (mat (a : GU σ n) i j - (F a i j : K)) - (mat (a' : GU σ n) i j - (F a' i j : K)) := by
      rw [haa']; ring
    rw [e]
    exact Valuation.map_sub_le _ (hF a i j) (hF a' i j)
  have key : ∀ a a' : KU σ n, F a = F a' →
      (((a' : GU σ n) * s : GU σ n) : GU σ n ⧸ KU σ n) = (((a : GU σ n) * s : GU σ n) : GU σ n ⧸ KU σ n) := by
    intro a a' haa'
    apply QuotientGroup.eq.2
    apply mem_KU_of_entries
    · have hg : ((a' : GU σ n) * s)⁻¹ * ((a : GU σ n) * s) = s⁻¹ * (a' : GU σ n)⁻¹ * (a : GU σ n) * s := by
        group
      rw [hg]
      exact half a a' haa'
    · have hg : (((a' : GU σ n) * s)⁻¹ * ((a : GU σ n) * s))⁻¹ = s⁻¹ * (a : GU σ n)⁻¹ * (a' : GU σ n) * s := by
        group
      rw [hg]
      exact half a' a haa'.symm
  haveI : Finite T := hTf.to_subtype
  classical
  let G : (Fin n → Fin n → T) → GU σ n ⧸ KU σ n := fun τ =>
    if h : ∃ a, F a = τ then (((h.choose : GU σ n) * s : GU σ n) : GU σ n ⧸ KU σ n) else ((1 : GU σ n) : GU σ n ⧸ KU σ n)
  apply (Set.finite_range G).subset
  rintro c ⟨a, ha, rfl⟩
  refine ⟨F ⟨a, ha⟩, ?_⟩
  have h : ∃ a', F a' = F ⟨a, ha⟩ := ⟨_, rfl⟩
  simp only [G, dif_pos h]
  exact key ⟨a, ha⟩ h.choose h.choose_spec.symm

end GlobalTheory.SatInd.DCoset
