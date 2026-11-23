import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def BlockSplit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (J : Type) [Fintype J] (n : ℕ) (z : O), z ≠ 0 →
    ∀ A : J → Matrix (Fin n) (Fin n) O, ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O) →
      ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O) (Q : Matrix (Fin n) (Fin (ν j)) O),
        P * A j * Q = z • (1 : Matrix (Fin (ν j)) (Fin (ν j)) O)

def RhoSumLatticeMaps : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a : ℕ) (A B : TT → ℕ),
    (∀ s, A s + B s + 1 ≤ 8 * a) →
    ∃ (io : ∀ j : TT → ℕ, Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s)) →ₗ[R.Kf]
        VHH (m := m) R.Kf TT (ex A) (ex B))
      (pr : ∀ j : TT → ℕ, VHH (m := m) R.Kf TT (ex A) (ex B) →ₗ[R.Kf]
        Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s))),
      (∀ x, ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)), io j (pr j x) = x) ∧
      ∀ (t c : ℕ) (e : Edge R.W R.Qq (m + 1)), IsEdge p n' 1 e →
        ∀ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)),
        (∀ x ∈ CCe p R.ι R.σ R.w TT (ex A) (ex B) t c e,
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • pr j x ∈
            CCL R (flatW m (fun s => A s - j s) (fun s => B s - j s)) t c e) ∧
        (∀ Φ ∈ CCe' p R.ι R.σ R.w TT (ex A) (ex B) t c e,
          ((p : R.Kf) ^ (((2 * (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) : ℕ) : ℤ) + AHH TT (ex A) (ex B) -
              Ar 1 (flatW m (fun s => A s - j s) (fun s => B s - j s)))) • (Φ ∘ₗ io j) ∈
            CCL' R (flatW m (fun s => A s - j s) (fun s => B s - j s)) t c e)

theorem vO_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {z : O} (hz : z ≠ 0) :
    vO p z = (((((IsDiscreteValuationRing.addVal O z).toNat : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  classical
  have hz' : algebraMap O (KK O) z ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hz
  simp only [vO, vK, ordW, if_neg hz']
  set ab := Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) with hab
  have hspec : algebraMap O (KK O) z * algebraMap O (KK O) (ab.2 : O) = algebraMap O (KK O) ab.1 :=
    Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  have h1 : z * (ab.2 : O) = ab.1 := IsFractionRing.injective O (KK O) (by rw [map_mul]; exact hspec)
  have hb0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.ne_zero ab.2.2
  have hv : IsDiscreteValuationRing.addVal O ab.1 =
      IsDiscreteValuationRing.addVal O z + IsDiscreteValuationRing.addVal O (ab.2 : O) := by
    rw [← h1, IsDiscreteValuationRing.addVal_mul]
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hbt : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [hv, ENat.toNat_add hzt hbt]
  simp only [WithTop.map_coe]
  congr 1
  push_cast
  ring

theorem vLEO_pow_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp0 : (p : O) ≠ 0) (hpm : ¬ IsUnit (p : O)) {z : O} (hz : z ≠ 0) {D : ℝ} (k : ℕ) (h : vLEO p z D) :
    vLEO p ((p : O) ^ k * z) (D + k) := by
  obtain ⟨q, hq, hqD⟩ := h
  have hpz : (p : O) ^ k * z ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hz
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  set t := (IsDiscreteValuationRing.addVal O z).toNat with ht
  have hpa : IsDiscreteValuationRing.addVal O (p : O) = ((ramE p O : ℕ) : ℕ∞) := (ENat.coe_toNat hpt).symm
  have hza : IsDiscreteValuationRing.addVal O z = (t : ℕ∞) := (ENat.coe_toNat hzt).symm
  have hsum : IsDiscreteValuationRing.addVal O ((p : O) ^ k * z) = ((k * ramE p O + t : ℕ) : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hpa, hza]
    push_cast; ring
  have he : (ramE p O : ℚ) ≠ 0 := by
    have h0 : ramE p O ≠ 0 := by
      intro h0
      apply hpm
      rw [← IsDiscreteValuationRing.addVal_eq_zero_iff, hpa, h0]
      simp
    exact_mod_cast h0
  rw [vO_eq hz] at hq
  have hq' : ((t : ℤ) : ℚ) / (ramE p O : ℚ) = q := WithTop.coe_injective hq
  refine ⟨q + k, ?_, by push_cast; linarith⟩
  rw [vO_eq hpz, hsum, ENat.toNat_coe, ← hq']
  congr 1
  push_cast
  field_simp
  ring

theorem rho_sum_bound_of_maps_splitting (hM : RhoSumLatticeMaps) (hBS : BlockSplit) : RhoSumLowerBoundEdge := by
  classical
  intro p n' R m hm TT a A B hdeg t c D X e he hD hρ
  obtain ⟨io, pr, hsum, hST⟩ := hM p n' R m hm TT a A B hdeg
  obtain ⟨n, hXn, hfac⟩ := hρ
  set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf
  rcases hfac with h0 | ⟨x, y, hx, hy, z, Mat, hz, hvz, hG⟩
  · subst h0
    refine ⟨fun _ => 0, fun j _ => Or.inl rfl, ?_⟩
    simpa using hXn
  generalize hu : TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊ = u at hST
  have hp0 : (p : R.Kf) ≠ 0 := by
    rw [R.p_eq]; exact pow_ne_zero _ R.w_ne
  have hinj : Function.Injective (algebraMap R.O R.Kf) := by
    have := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  let xs : ∀ j : TT → ℕ, Fin n → Vsp R.Kf (lamj j) := fun j i => ((p : R.Kf) ^ u) • pr j (x i)
  let ys : ∀ j : TT → ℕ, Fin n → Module.Dual R.Kf (Vsp R.Kf (lamj j)) := fun j l =>
    ((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (y l ∘ₗ io j)
  have hxs : ∀ j ∈ Jf, ∀ i, xs j i ∈ CCL R (lamj j) t c e := fun j hj i => (hST t c e he j hj).1 _ (hx i)
  have hys : ∀ j ∈ Jf, ∀ l, ys j l ∈ CCL' R (lamj j) t c e := fun j hj l => (hST t c e he j hj).2 _ (hy l)
  have hkey : ∀ j i l, be p 1 (lamj j) (xs j i) (ys j l) =
      (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) := by
    intro j i l
    show (((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (y l ∘ₗ io j))
      (((p : R.Kf) ^ Ar 1 (lamj j)) • (((p : R.Kf) ^ u) • pr j (x i))) =
      (p : R.Kf) ^ (3 * u) * (y l) (((p : R.Kf) ^ AHH TT (ex A) (ex B)) • io j (pr j (x i)))
    rw [LinearMap.smul_apply, map_smul, map_smul, map_smul, LinearMap.comp_apply]
    simp only [smul_eq_mul]
    have hc : (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) *
        ((p : R.Kf) ^ Ar 1 (lamj j) * (p : R.Kf) ^ u) = (p : R.Kf) ^ (3 * u) * (p : R.Kf) ^ AHH TT (ex A) (ex B) := by
      rw [← zpow_natCast (p : R.Kf) u, ← zpow_natCast (p : R.Kf) (3 * u), ← zpow_add₀ hp0, ← zpow_add₀ hp0,
        ← zpow_add₀ hp0]
      congr 1
      push_cast
      ring
    linear_combination (y l) (io j (pr j (x i))) * hc
  have hint : ∀ (j : Jf) (i l : Fin n), ∃ g : R.O, be p 1 (lamj j) (xs j i) (ys j l) = algebraMap R.O R.Kf g :=
    fun j i l => be_Re R (lamj j) e (hxs j j.2 i).1.2 (hys j j.2 l).1.2
  choose g hg using hint
  let Aj : Jf → Matrix (Fin n) (Fin n) R.O := fun j => (Matrix.of (g j)) * Mat
  have hz' : (p : R.O) ^ (3 * u) * z ≠ 0 := mul_ne_zero (pow_ne_zero _ R.p_ne) hz
  have hsumA : ∑ j, Aj j = ((p : R.O) ^ (3 * u) * z) • (1 : Matrix (Fin n) (Fin n) R.O) := by
    ext i k
    apply hinj
    rw [Matrix.sum_apply, map_sum]
    have e1 : ∀ j : Jf, algebraMap R.O R.Kf (Aj j i k) =
        ∑ l, (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) *
          algebraMap R.O R.Kf (Mat l k) := by
      intro j
      simp only [Aj, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, ← hg, hkey]
    simp only [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ l, ∑ j : Jf, (p : R.Kf) ^ (3 * u) * beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) *
          algebraMap R.O R.Kf (Mat l k) =
        (p : R.Kf) ^ (3 * u) * (beHH (m := m) p TT (ex A) (ex B) (x i) (y l) * algebraMap R.O R.Kf (Mat l k)) := by
      intro l
      have e3 : ∑ j : Jf, beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l) =
          beHH (m := m) p TT (ex A) (ex B) (x i) (y l) := by
        rw [Finset.sum_coe_sort Jf (fun j => beHH (m := m) p TT (ex A) (ex B) (io j (pr j (x i))) (y l))]
        unfold beHH
        rw [← map_sum, ← Finset.smul_sum, hsum]
      rw [← e3, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    rw [← Finset.mul_sum, hG i k, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, map_mul, map_pow, map_natCast]
    · rw [mul_zero, mul_zero, map_zero]
  obtain ⟨ν, hν, hPQ⟩ := hBS R.O Jf n _ hz' Aj hsumA
  choose P Q hPQ' using hPQ
  refine ⟨fun j => if h : j ∈ Jf then ν ⟨j, h⟩ else 0, ?_, ?_⟩
  · intro j hj
    have hjm : j ∈ Jf := Fintype.mem_piFinset.2 fun s => Finset.mem_range.2 (Nat.lt_succ_of_le (hj s))
    have hnj : (if h : j ∈ Jf then ν ⟨j, h⟩ else 0) = ν ⟨j, hjm⟩ := dif_pos hjm
    beta_reduce
    rw [hnj]
    set jj : Jf := ⟨j, hjm⟩ with hjj
    right
    let x' : Fin (ν jj) → Vsp R.Kf (lamj j) := fun a' => ∑ i, algebraMap R.O R.Kf (P jj a' i) • xs j i
    let y' : Fin (ν jj) → Module.Dual R.Kf (Vsp R.Kf (lamj j)) := fun b' => ∑ l, (Mat * Q jj) l b' • ys j l
    have e4 : ∀ a' l', be p 1 (lamj j) (x' a') (y' l') = algebraMap R.O R.Kf ((P jj * Aj jj * Q jj) a' l') := by
      intro a' l'
      show be p 1 (lamj j) (∑ i, algebraMap R.O R.Kf (P jj a' i) • xs j i) (∑ l, (Mat * Q jj) l l' • ys j l) = _
      rw [be_sum_left, Matrix.mul_assoc]
      simp only [be_sum, Matrix.mul_apply, map_sum, map_mul, Aj, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hgj : ∀ l, be p 1 (lamj j) (xs j i) (ys j l) = algebraMap R.O R.Kf (g jj i l) := fun l => hg jj i l
      simp only [hgj]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l1 _ => Finset.sum_congr rfl fun l2 _ => by ring
    refine ⟨x', y', ?_, ?_, (p : R.O) ^ (3 * u) * z, 1, hz', ?_, ?_⟩
    · intro a'
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (hxs j hjm i)
    · intro b'
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hys j hjm l)
    · have h1 := vLEO_pow_mul R.p_ne R.p_not_unit hz (3 * u) hvz
      refine vLEO_mono ?_ h1
      have : ((3 * u : ℕ) : ℝ) ≤ 4 * (TT.card : ℝ) * (⌈((m : ℝ) + 2) * lgA p a m⌉₊ : ℕ) := by
        rw [← hu]; push_cast
        have : (0 : ℝ) ≤ (TT.card : ℝ) * (⌈((m : ℝ) + 2) * lgA p a m⌉₊ : ℕ) := by positivity
        linarith
      linarith
    · intro a' b'
      show ∑ l', be p 1 (lamj j) (x' a') (y' l') * algebraMap R.O R.Kf ((1 : Matrix (Fin (ν jj)) (Fin (ν jj)) R.O) l' b') =
        if a' = b' then algebraMap R.O R.Kf ((p : R.O) ^ (3 * u) * z) else 0
      simp only [e4, hPQ']
      rw [Finset.sum_eq_single b' (fun l' _ hl' => by rw [Matrix.one_apply_ne hl', map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)]
      rw [Matrix.one_apply_eq, map_one, mul_one, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
  · have h1 : (∑ j ∈ Jf, (((if h : j ∈ Jf then ν ⟨j, h⟩ else 0 : ℕ)) : ℝ)) = ((∑ j : Jf, ν j : ℕ) : ℝ) := by
      rw [← Finset.sum_coe_sort Jf (fun j => (((if h : j ∈ Jf then ν ⟨j, h⟩ else 0 : ℕ)) : ℝ))]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dif_pos j.2]
    rw [h1]
    exact le_trans hXn (by exact_mod_cast hν)

end Formalism.MainNotions.flipOneThree.Pf

end
