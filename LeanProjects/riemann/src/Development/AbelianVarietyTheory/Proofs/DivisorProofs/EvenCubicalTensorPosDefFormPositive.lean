import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TPos

open Finset

theorem lagrange_decomp : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ), (∀ i j, A i j = A j i) →
    (∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j) →
    ∃ N : ℕ, 0 < N ∧ ∃ (k : ℕ) (n : Fin k → ℕ) (m : Fin k → Fin r → ℤ),
      ∀ i j, (N : ℤ) * A i j = ∑ l, (n l : ℤ) * m l i * m l j := by
  intro r
  induction r with
  | zero => intro A _ _; exact ⟨1, one_pos, 0, Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro A hs hp
    have ha : 0 < A 0 0 := by
      have h := hp (fun i => if i = 0 then 1 else 0) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Fin.sum_univ_succ, Fin.succ_ne_zero] using h
    set a := A 0 0 with ha_def
    set c : Fin r → ℤ := fun j => A 0 j.succ with hc
    set S : Matrix (Fin r) (Fin r) ℤ := fun i j => a * A i.succ j.succ - c i * c j with hS
    have hSs : ∀ i j, S i j = S j i := by
      intro i j; simp only [hS]; rw [hs i.succ j.succ]; ring
    have hSp : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (S i j : ℚ) * v j := by
      intro v hv
      set s : ℚ := ∑ j, (c j : ℚ) * v j with hs_def
      set Q : ℚ := ∑ i, ∑ j, v i * (A i.succ j.succ : ℚ) * v j with hQ
      have haq : (0:ℚ) < a := by exact_mod_cast ha
      have h1 : ∑ i, ∑ j, v i * (S i j : ℚ) * v j = a * Q - s * s := by
        have e : ∀ i j, v i * (S i j : ℚ) * v j
            = a * (v i * (A i.succ j.succ : ℚ) * v j) - ((c i : ℚ) * v i) * ((c j : ℚ) * v j) := by
          intro i j; rw [show S i j = a * A i.succ j.succ - c i * c j from rfl]; push_cast; ring
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j, hQ, hs_def,
          Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      set u : Fin (r+1) → ℚ := Fin.cons (-s / a) v with hu
      have hu0 : u ≠ 0 := by
        intro h; apply hv; funext j; have := congrFun h j.succ; simpa [hu] using this
      have h2 : ∑ i, ∑ j, u i * (A i j : ℚ) * u j = Q - s * s / a := by
        simp only [Fin.sum_univ_succ, hu, Fin.cons_zero, Fin.cons_succ]
        have e1 : ∑ j : Fin r, -s / a * (A 0 j.succ : ℚ) * v j = -s / a * s := by
          rw [hs_def, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp only [hc]; ring
        have e2 : ∑ i : Fin r, (v i * (A i.succ 0 : ℚ) * (-s / a) +
            ∑ j : Fin r, v i * (A i.succ j.succ : ℚ) * v j) = -s / a * s + Q := by
          rw [Finset.sum_add_distrib, hQ, hs_def, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by rw [hs i.succ 0]; simp only [hc]; ring
        rw [e1, e2]
        field_simp
        ring
      have h3 := hp u hu0
      rw [h2] at h3
      rw [h1]
      have : a * Q - s * s = a * (Q - s * s / a) := by field_simp
      rw [this]; exact mul_pos haq h3
    obtain ⟨N', hN', k, n, m, hm⟩ := ih S hSs hSp
    refine ⟨N' * a.toNat, Nat.mul_pos hN' (by omega), k + 1, Fin.cons N' n,
      Fin.cons (fun j => A 0 j) (fun l => Fin.cons 0 (m l)), ?_⟩
    have haN : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    intro i j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, haN]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [ha_def]
    · simp [ha_def]
    · simp; rw [hs i.succ 0]; ring
    · simp only [Fin.cons_succ]
      rw [← hm i j]; simp only [hS, hc]; ring

theorem zpow_fsum {G I : Type} [CommGroup G] (a : G) (s : Finset I) (f : I → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensor_pos : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ z : Fin r → X, z ≠ 0 → ∃ s ∈ maximalIdeal R, ((∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax r W hW z hz
  classical
  let B : X → X → (FractionRing R)ˣ := fun a b => κ (a + b) * (κ a)⁻¹ * (κ b)⁻¹
  have h0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_left_cancel (a := κ 0 * κ 0 * κ 0) (by rw [_root_.mul_one]; exact h)
  have hB1 : ∀ a a' b, B (a + a') b = B a b * B a' b := by
    intro a a' b
    have e : κ (a + a' + b) = κ (a + a') * κ (a + b) * κ (a' + b) * (κ a * κ a' * κ b)⁻¹ := by
      rw [← hcub a a' b]; group
    simp only [B]; rw [e]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := (κ a).ne_zero; have := (κ a').ne_zero; have := (κ b).ne_zero
    have := (κ (a + a')).ne_zero; have := (κ (a + b)).ne_zero; have := (κ (a' + b)).ne_zero
    field_simp
  have hBs : ∀ a b, B a b = B b a := by
    intro a b; simp only [B]; rw [add_comm]; exact mul_right_comm _ _ _
  have hB0 : ∀ b, B 0 b = 1 := by intro b; simp [B, h0]
  have hBd : ∀ a, B a a = κ a ^ 2 := by
    intro a
    have h := hB1 a (-a) a
    rw [add_neg_cancel, hB0] at h
    have hm : B (-a) a = (κ a)⁻¹ * (κ a)⁻¹ := by simp [B, h0, hneg]
    rw [hm] at h
    have := eq_inv_of_mul_eq_one_left h.symm
    rw [this]; group
  let f : X → Multiplicative X →* (FractionRing R)ˣ := fun w =>
    { toFun := fun a => B (Multiplicative.toAdd a) w
      map_one' := hB0 w
      map_mul' := fun a b => hB1 _ _ _ }
  have hBsum : ∀ (c : Fin r → ℤ) (w : X), B (∑ i, c i • z i) w = ∏ i, B (z i) w ^ c i := by
    intro c w
    have e : Multiplicative.ofAdd (∑ i, c i • z i) = ∏ i, (Multiplicative.ofAdd (z i)) ^ c i := by
      simp [ofAdd_sum, ofAdd_zsmul]
    have := congrArg (f w) e
    rw [map_prod] at this
    simp only [map_zpow] at this
    exact this
  have hBn : ∀ (M : ℕ) a w, B (M • a) w = B a w ^ M := by
    intro M a w
    induction M with
    | zero => simp [hB0]
    | succ M ih => rw [succ_nsmul, hB1, ih, pow_succ]
  have hQ : ∀ c : Fin r → ℤ,
      ∏ i, ∏ j, B (z i) (z j) ^ (c i * c j) = κ (∑ i, c i • z i) ^ 2 := by
    intro c
    rw [← hBd, hBsum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hBs, hBsum, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hBs, ← zpow_mul, mul_comm]

  set A : Matrix (Fin r) (Fin r) ℤ := W + W.transpose with hA
  have hAij : ∀ i j, A i j = W i j + W j i := fun i j => rfl
  have hAs : ∀ i j, A i j = A j i := fun i j => by rw [hAij, hAij, add_comm]
  have hApos : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j := by
    intro v hv
    have hv' : (fun i => (v i : ℝ)) ≠ 0 := by
      intro h; apply hv; funext i; have := congrFun h i; simpa using this
    have h := hW.dotProduct_mulVec_pos hv'
    have e : dotProduct (star (fun i => (v i : ℝ))) ((A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)))
        = ((∑ i, ∑ j, v i * (A i j : ℚ) * v j : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
    rw [e] at h
    exact_mod_cast h
  obtain ⟨N, hN, k, n, m, hm⟩ := lagrange_decomp r A hAs hApos
  set x : (FractionRing R)ˣ := ∏ i, ∏ j, B (z i) (z j) ^ W i j with hx
  have hx2 : x ^ 2 = ∏ i, ∏ j, B (z i) (z j) ^ A i j := by
    have e1 : ∏ i, ∏ j, B (z i) (z j) ^ A i j
        = (∏ i, ∏ j, B (z i) (z j) ^ W i j) * ∏ i, ∏ j, B (z i) (z j) ^ W j i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hAij, zpow_add]
    have e2 : ∏ i, ∏ j, B (z i) (z j) ^ W j i = ∏ i, ∏ j, B (z i) (z j) ^ W i j := by
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [hBs]
    rw [e1, e2, pow_two]
  let y : Fin k → X := fun l => ∑ i, m l i • z i
  have hxN : x ^ (2 * N) = ∏ l, κ (y l) ^ (2 * n l) := by
    calc x ^ (2 * N) = (x ^ 2) ^ N := pow_mul x 2 N
      _ = ∏ i, ∏ j, B (z i) (z j) ^ ((N : ℤ) * A i j) := by
        rw [hx2, ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm]
      _ = ∏ i, ∏ j, ∏ l, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
        rw [hm, zpow_fsum]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
      _ = ∏ i, ∏ l, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
      _ = ∏ l, ∏ i, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := Finset.prod_comm
      _ = ∏ l, κ (y l) ^ (2 * n l) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [pow_mul, show y l = ∑ i, m l i • z i from rfl, ← hQ (m l)]
        simp only [Finset.prod_pow]
  have hs : ∀ l, ∃ t : R, ((κ (y l) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ t ∧
      (y l ≠ 0 → t ∈ maximalIdeal R) := by
    intro l
    by_cases h : y l = 0
    · exact ⟨1, by rw [h, h0]; simp, fun h' => absurd h h'⟩
    · obtain ⟨t, ht, e⟩ := hmax _ h; exact ⟨t, e, fun _ => ht⟩
  choose s hs1 hs2 using hs
  have hxK : ((x : (FractionRing R)ˣ) : FractionRing R) ^ (2 * N)
      = algebraMap R _ (∏ l, s l ^ (2 * n l)) := by
    rw [← Units.val_pow_eq_pow_val, hxN, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Units.val_pow_eq_pow_val, hs1, map_pow]
  have hint : IsIntegral R ((x : (FractionRing R)ˣ) : FractionRing R) :=
    IsIntegral.of_pow (by omega : 0 < 2 * N) (hxK ▸ isIntegral_algebraMap)
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have htN : t ^ (2 * N) = ∏ l, s l ^ (2 * n l) := by
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_pow, ht, hxK]
  have hdet : A.det ≠ 0 := by
    have h := hW.det_pos
    have e : (A.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) := by
      have := (Int.castRingHom ℝ).map_det A
      exact this.symm
    rw [e] at h
    exact_mod_cast h.ne'
  have hex : ∃ l, n l ≠ 0 ∧ y l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hrow : ∀ i, ∑ j, ((N : ℤ) * A i j) • z j = 0 := by
      intro i
      simp_rw [hm i, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      have : ∑ j, ((n l : ℤ) * m l i * m l j) • z j = ((n l : ℤ) * m l i) • y l := by
        simp only [y, Finset.smul_sum, mul_smul]
      rw [this]
      by_cases hn : n l = 0
      · simp [hn]
      · rw [hcon l hn, smul_zero]
    have hcol : ∀ q, ((N : ℤ) * A.det) • z q = 0 := by
      intro q
      have h1 : ∑ i, A.adjugate q i • ∑ j, ((N : ℤ) * A i j) • z j = 0 := by
        simp [hrow]
      rw [← h1]
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ j, ∑ i, A.adjugate q i * ((N : ℤ) * A i j) = (N : ℤ) * (A.adjugate * A) q j := by
        intro j; rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [this, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      simp [Finset.sum_ite_eq, mul_comm]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hz
    have hq' : z q ≠ 0 := hq
    have hD : (N : ℤ) * A.det ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hdet
    have hM : ((N : ℤ) * A.det).natAbs • z q = 0 := by
      rcases Int.natAbs_eq ((N : ℤ) * A.det) with h | h
      · rw [← natCast_zsmul, ← h]; exact hcol q
      · have := hcol q; rw [h, neg_smul, neg_eq_zero, natCast_zsmul] at this; exact this
    have hk1 : κ (z q) ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := by
      rw [pow_mul, ← hBd, ← hBn, hM, hB0]
    obtain ⟨s', hs', e'⟩ := hmax _ hq'
    have h1 : s' ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ← e', map_one, ← Units.val_pow_eq_pow_val, hk1, Units.val_one]
    have hpos := Int.natAbs_pos.mpr hD
    have hunit : IsUnit s' := IsUnit.of_pow_eq_one h1 (by omega)
    exact (IsLocalRing.mem_maximalIdeal _).mp hs' hunit
  obtain ⟨l0, hn0, hy0⟩ := hex
  have hprod : ∏ l, s l ^ (2 * n l) ∈ maximalIdeal R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l0)]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (hs2 l0 hy0) _ (by omega))
  refine ⟨t, ?_, ht.symm⟩
  exact (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem (2 * N) (htN ▸ hprod)

end GlobalTheory.Mum.TPos
