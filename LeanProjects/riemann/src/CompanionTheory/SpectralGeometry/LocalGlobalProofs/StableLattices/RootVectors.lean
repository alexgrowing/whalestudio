import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuRootVec

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mul_single_mul_entry {n : ℕ} (A B : Mat n) (a b i l : Fin n) (c : ℂ) :
    (A * single a b c * B) i l = A i a * c * B b l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    rw [Matrix.mul_single_apply_of_ne (hbj := hj), zero_mul]
  · simp

theorem ex_of_mul_self_eq_zero {n : ℕ} (Y : Mat n) (hY : Y * Y = 0) (τ : ℝ) :
    ex Y τ = 1 + (τ : ℂ) • Y := by
  unfold ex
  have h2 : ((τ : ℂ) • Y) ^ 2 = 0 := by
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, hY, smul_zero, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro m hm
    have : 2 ≤ m := by
      have := Finset.mem_range.not.1 hm
      omega
    rw [pow_eq_zero_of_le this h2, smul_zero]

variable {k r : ℕ}

theorem Hq_row {i i' : Fin (2 * r + k + 1)} (hi : outer k r i) (h : i.val + i'.val = 2 * r + k)
    (l : Fin (2 * r + k + 1)) : Hq k r i l = if l = i' then 1 else 0 := by
  simp only [Hq, hi, if_true, Fin.ext_iff]
  congr 1
  apply propext; omega

theorem Hq_col {i i' : Fin (2 * r + k + 1)} (hi : outer k r i) (h : i.val + i'.val = 2 * r + k)
    (l : Fin (2 * r + k + 1)) : Hq k r l i = if l = i' then 1 else 0 := by
  simp only [Hq, outer, Fin.ext_iff] at *
  split_ifs <;> first | rfl | omega

theorem Hq_mul_single {i i' : Fin (2 * r + k + 1)} (hi : outer k r i) (h : i.val + i'.val = 2 * r + k)
    (l : Fin (2 * r + k + 1)) (c : ℂ) : Hq k r * single i l c = single i' l c := by
  ext p q
  have := mul_single_mul_entry (Hq k r) 1 i l p q c
  rw [Matrix.mul_one] at this
  rw [this, Hq_col hi h, Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : i' = p <;> by_cases h2 : l = q <;> simp [h1, h2, @eq_comm _ p i']

theorem single_mul_Hq {i i' : Fin (2 * r + k + 1)} (hi : outer k r i) (h : i.val + i'.val = 2 * r + k)
    (l : Fin (2 * r + k + 1)) (c : ℂ) : single l i c * Hq k r = single l i' c := by
  ext p q
  have := mul_single_mul_entry 1 (Hq k r) l i p q c
  rw [Matrix.one_mul] at this
  rw [this, Hq_row hi h, Matrix.one_apply, Matrix.single_apply]
  by_cases h1 : l = p <;> by_cases h2 : i' = q <;> simp [h1, h2, @eq_comm _ p l, @eq_comm _ q i']

theorem dg_Hq {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) :
    (dg d)ᴴ * Hq k r * dg d = Hq k r := by
  obtain ⟨-, h1, h2, -⟩ := hd
  ext i j
  simp only [dg, diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Hq]
  split_ifs with a b c
  · have := h1 i j a b
    rw [mul_one, ← Complex.ofReal_mul, this, Complex.ofReal_one]
  · simp
  · subst c; simp [h2 i a]
  · simp

def nxtS (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val - 1, by omega⟩

def rootE (k r : ℕ) (a : Fin r) (κ : ℂ) : Mat (2 * r + k + 1) :=
  single (eI k r a) (nxt k r a) κ - single (nxtS k r a) (esI k r a) (conj κ)

theorem rootE_lie (a : Fin r) (κ : ℂ) : Lie (Hq k r) (rootE k r a κ) := by
  have ha := a.isLt
  unfold Lie rootE
  rw [conjTranspose_sub, conjTranspose_single, conjTranspose_single, Matrix.sub_mul, Matrix.mul_sub,
    single_mul_Hq (i := eI k r a) (i' := esI k r a) (by simp only [outer, eI]; omega)
      (by simp only [eI, esI]; omega),
    single_mul_Hq (i := nxtS k r a) (i' := nxt k r a) (by simp only [outer, nxtS]; omega)
      (by simp only [nxtS, nxt]; omega),
    Hq_mul_single (i := eI k r a) (i' := esI k r a) (by simp only [outer, eI]; omega)
      (by simp only [eI, esI]; omega),
    Hq_mul_single (i := nxtS k r a) (i' := nxt k r a) (by simp only [outer, nxtS]; omega)
      (by simp only [nxtS, nxt]; omega)]
  simp

theorem rootE_sq (hk : 1 ≤ k) (a : Fin r) (κ : ℂ) : rootE k r a κ * rootE k r a κ = 0 := by
  have ha := a.isLt
  unfold rootE
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    single_mul_single_of_ne (h := by simp only [nxt, eI, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [nxt, nxtS, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [esI, eI, Ne, Fin.ext_iff]; omega),
    single_mul_single_of_ne (h := by simp only [esI, nxtS, Ne, Fin.ext_iff]; omega)]
  simp

theorem dg_rootE {d : Fin (2 * r + k + 1) → ℝ} (hd : IsTor k r d) (a : Fin r) (κ : ℂ) :
    dg d * rootE k r a κ = ((d (eI k r a) / d (nxt k r a) : ℝ) : ℂ) • (rootE k r a κ * dg d) := by
  have ha := a.isLt
  obtain ⟨h0, h1, -, -⟩ := hd
  have e1 := h1 (eI k r a) (esI k r a) (by simp only [outer, eI]; omega) (by simp only [eI, esI]; omega)
  have e2 := h1 (nxtS k r a) (nxt k r a) (by simp only [outer, nxtS]; omega)
    (by simp only [nxtS, nxt]; omega)
  have hn := (h0 (nxt k r a)).ne'
  have f1 : d (eI k r a) = d (eI k r a) / d (nxt k r a) * d (nxt k r a) := by field_simp
  have f2 : d (nxtS k r a) = d (eI k r a) / d (nxt k r a) * d (esI k r a) := by
    field_simp; rw [e1, e2]
  generalize d (eI k r a) / d (nxt k r a) = α at f1 f2
  ext p q
  simp only [dg, rootE, diagonal_mul, mul_diagonal, Matrix.smul_apply, Matrix.sub_apply, single_apply,
    smul_eq_mul]
  have g1 : (d p : ℂ) * (if eI k r a = p ∧ nxt k r a = q then κ else 0) =
      α * ((if eI k r a = p ∧ nxt k r a = q then κ else 0) * d q) := by
    split_ifs with h
    · rw [← h.1, ← h.2, f1]; push_cast; ring
    · simp
  have g2 : (d p : ℂ) * (if nxtS k r a = p ∧ esI k r a = q then conj κ else 0) =
      α * ((if nxtS k r a = p ∧ esI k r a = q then conj κ else 0) * d q) := by
    split_ifs with h
    · rw [← h.1, ← h.2, f2]; push_cast; ring
    · simp
  rw [mul_sub, g1, g2]; ring

theorem norm_conj_rootE {R : Mat (2 * r + k + 1)} (hR : Rᴴ * R = 1) (a : Fin r) (κ : ℂ) :
    ‖Rᴴ * rootE k r a κ * R‖ ≤ 2 * ‖κ‖ := by
  have hb : ∀ i j, ‖R i j‖ ≤ 1 := fun i j =>
    entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hR) i j
  have key : ∀ (p q i l : Fin (2 * r + k + 1)) (c : ℂ), ‖(Rᴴ * single p q c * R) i l‖ ≤ ‖c‖ := by
    intro p q i l c
    rw [mul_single_mul_entry, norm_mul, norm_mul, conjTranspose_apply, norm_star]
    calc ‖R p i‖ * ‖c‖ * ‖R q l‖ ≤ 1 * ‖c‖ * 1 := by gcongr <;> apply hb
      _ = ‖c‖ := by ring
  rw [Matrix.norm_le_iff (by positivity)]
  intro i l
  rw [rootE, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  have h1 := key (eI k r a) (nxt k r a) i l κ
  have h2 := key (nxtS k r a) (esI k r a) i l (conj κ)
  rw [Complex.norm_conj] at h2
  linarith

theorem col_of_mulVec {n : ℕ} {A : Mat n} {j : Fin n} (h : A *ᵥ bvec j = bvec j) (i : Fin n) :
    A i j = if i = j then 1 else 0 := by
  have := congrFun h i
  simpa [bvec, Pi.single_apply] using this

theorem frame_row {Γ : Mat (2 * r + k + 1)} (hΓ : Γᴴ * Hpk k r * Γ = Hq k r)
    {i i' : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (h : i.val + i'.val = 2 * r + k)
    (hf : Γ *ᵥ bvec i = bvec i) (l : Fin (2 * r + k + 1)) : Γ i' l = if l = i' then 1 else 0 := by
  have h1 := congrFun (congrFun hΓ i) l
  rw [Hq_row (i' := i') (by simp only [outer]; omega) h, Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single i, conjTranspose_apply, col_of_mulVec hf, if_pos rfl, star_one, one_mul,
    Matrix.mul_apply, Finset.sum_eq_single i'] at h1
  · rw [← h1]
    have : Hpk k r i i' = 1 := by
      simp only [Hpk]
      split_ifs <;> first | rfl | omega
    rw [this, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i'.val := fun e => hb (Fin.ext e)
    have : Hpk k r i b = 0 := by
      simp only [Hpk]
      split_ifs <;> first | rfl | omega
    rw [this, zero_mul]
  · simp
  · intro b _ hb
    rw [conjTranspose_apply, col_of_mulVec hf, if_neg hb, star_zero, zero_mul]
  · simp

theorem inv_row {n : ℕ} {Γ : Mat n} (hu : IsUnit Γ.det) {i : Fin n}
    (h : ∀ l, Γ i l = if l = i then 1 else 0) (l : Fin n) : Γ⁻¹ i l = if l = i then 1 else 0 := by
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv Γ hu) i) l
  rw [Matrix.mul_apply] at h1
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [h1, Matrix.one_apply]
  simp only [eq_comm]

theorem inv_mulVec_fix {n : ℕ} {Γ : Mat n} (hu : IsUnit Γ.det) (v : Fin n → ℂ) :
    Γ⁻¹ *ᵥ (Γ *ᵥ v) = v := by
  rw [mulVec_mulVec, Matrix.nonsing_inv_mul Γ hu, one_mulVec]

theorem rootVec : RootVec := by
  intro k r z Γ c hk hA hc
  obtain ⟨hΓ, hfix, ρ, hρ, hz⟩ := hA
  let κ : Fin r → ℂ := fun a => if a.val + 1 < r then (c a)⁻¹ else ((ρ : ℂ) * c a)⁻¹
  refine ⟨∑ a, 2 * ‖κ a‖, fun a d R hd hR hg => ?_⟩
  have ha := a.isLt
  have hHu : IsUnit (Hpk k r).det :=
    Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1
  obtain ⟨-, hmul, hinv⟩ := unitary_group_holds _ _ hHu
  have hgu := (hinv _ hg).1
  have hΓu : IsUnit Γ.det := by
    rw [det_mul, det_mul] at hgu
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hgu)
  have hR' : R * Rᴴ = 1 := mul_eq_one_comm.1 hR
  have hRq : Rᴴ * Hq k r * R = Hpk k r := by
    have h1 : (Γ * dg d * R)ᴴ * Hpk k r * (Γ * dg d * R) = Hpk k r := hg
    rw [← h1, ← dg_Hq hd, ← hΓ]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  set E := rootE k r a (κ a) with hE
  have hLie : Lie (Hpk k r) (Rᴴ * E * R) := by
    have h1 : Eᴴ * Hq k r + Hq k r * E = 0 := rootE_lie a (κ a)
    unfold Lie
    rw [← hRq]
    calc (Rᴴ * E * R)ᴴ * (Rᴴ * Hq k r * R) + Rᴴ * Hq k r * R * (Rᴴ * E * R)
        = Rᴴ * (Eᴴ * (R * Rᴴ) * Hq k r + Hq k r * (R * Rᴴ) * E) * R := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_add,
            Matrix.add_mul]
      _ = 0 := by rw [hR', Matrix.mul_one, Matrix.mul_one, h1, Matrix.mul_zero, Matrix.zero_mul]
  have hsq : Rᴴ * E * R * (Rᴴ * E * R) = 0 := by
    calc Rᴴ * E * R * (Rᴴ * E * R) = Rᴴ * (E * (R * Rᴴ) * E) * R := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hR', Matrix.mul_one, hE, rootE_sq hk, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨Rᴴ * E * R, hLie, (norm_conj_rootE hR a (κ a)).trans
    (Finset.single_le_sum (f := fun a => 2 * ‖κ a‖) (fun _ _ => by positivity) (Finset.mem_univ a)),
    fun τ => ?_⟩
  have hmem : Γ * dg d * R * ex (Rᴴ * E * R) τ * (Γ * dg d * R)⁻¹ ∈ UH (Hpk k r) :=
    hmul _ (hmul _ hg _ (ex_mem_of_lie hLie τ)) _ (hinv _ hg).2
  set α : ℝ := d (eI k r a) / d (nxt k r a) with hα
  have hform : Γ * dg d * R * ex (Rᴴ * E * R) τ * (Γ * dg d * R)⁻¹ =
      1 + ((α * τ : ℝ) : ℂ) • (Γ * E * Γ⁻¹) := by
    have h1 : Γ * dg d * R * (Rᴴ * E * R) = (α : ℂ) • (Γ * E * Γ⁻¹ * (Γ * dg d * R)) := by
      calc Γ * dg d * R * (Rᴴ * E * R) = Γ * (dg d * ((R * Rᴴ) * E)) * R := by
            simp only [Matrix.mul_assoc]
        _ = (α : ℂ) • (Γ * E * (Γ⁻¹ * Γ) * dg d * R) := by
            rw [hR', Matrix.one_mul, hE, dg_rootE hd, Matrix.nonsing_inv_mul Γ hΓu, Matrix.mul_one,
              Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, hα]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [ex_of_mul_self_eq_zero _ hsq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ hgu, Matrix.mul_smul, h1, smul_smul, Matrix.smul_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hgu]
    congr 2
    push_cast; ring
  have rowS : ∀ (b : Fin r) l, Γ (esI k r b) l = if l = esI k r b then 1 else 0 := fun b =>
    frame_row hΓ (i := eI k r b) (by have := b.isLt; simp only [eI]; omega)
      (by have := b.isLt; simp only [eI, esI]; omega) (hfix b).1
  have rowE : ∀ (b : Fin r) l, Γ (eI k r b) l = if l = eI k r b then 1 else 0 := fun b =>
    frame_row hΓ (i := esI k r b) (by have := b.isLt; simp only [esI]; omega)
      (by have := b.isLt; simp only [eI, esI]; omega) (hfix b).2
  have colI : ∀ (b : Fin r) i, Γ⁻¹ i (eI k r b) = if i = eI k r b then 1 else 0 := fun b =>
    col_of_mulVec (by
      have := inv_mulVec_fix hΓu (bvec (eI k r b))
      rwa [(hfix b).1] at this)
  have hent : ∀ i l, (Γ * E * Γ⁻¹) i l =
      (if i = eI k r a then κ a * Γ⁻¹ (nxt k r a) l else 0) -
        (if l = esI k r a then Γ i (nxtS k r a) * conj (κ a) else 0) := by
    intro i l
    rw [hE, rootE, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, mul_single_mul_entry,
      mul_single_mul_entry, col_of_mulVec (hfix a).1, inv_row hΓu (rowS a)]
    split_ifs <;> simp
  rw [hform] at hmem ⊢
  generalize Γ * E * Γ⁻¹ = M at hent hmem ⊢
  refine ⟨⟨hmem, fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩, ?_⟩
  · have hb := b.isLt
    have : M i (eI k r b) = 0 := by
      rw [hent, colI, if_neg (c := eI k r b = esI k r a) (by simp only [eI, esI, Fin.ext_iff]; omega)]
      split_ifs with p q
      · exfalso; simp only [eI, nxt, Fin.ext_iff] at p q; omega
      · simp
      · simp
    simp [this, Matrix.one_apply]
  · have : M i j = 0 := by
      rw [hent, if_neg (by simp only [eI, Fin.ext_iff]; omega),
        if_neg (by simp only [esI, Fin.ext_iff]; omega), sub_zero]
    simp [this, Matrix.one_apply]
  · have hzr : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) →
        (∀ l, Γ i l = if l = i then 1 else 0) → z i = 0 := by
      intro i hi h
      have n1 : i ≠ wI k r 0 := by simp only [wI, Ne, Fin.ext_iff, Fin.val_zero]; omega
      have n2 : i ≠ wI k r (Fin.last k) := by simp only [wI, Ne, Fin.ext_iff, Fin.val_last]; omega
      rw [hz]
      simp [mulVec, dotProduct, h, bvec, n1, n2]
    have hzS : z (esI k r a) = 0 := hzr _ (by simp only [esI]; omega) (rowS a)
    have hell : ∀ b, c b * PI.BesselMapUniq.ellA k r z (1 + ((α * τ : ℝ) : ℂ) • M) b =
        if b = a then ((α * τ : ℝ) : ℂ) else 0 := by
      intro b
      have hb := b.isLt
      have hba : eI k r b = eI k r a ↔ b = a := by simp only [eI, Fin.ext_iff]
      unfold PI.BesselMapUniq.ellA
      by_cases h : b.val + 1 < r
      · rw [dif_pos h, Matrix.add_apply, Matrix.smul_apply, hent, colI,
          if_neg (c := _ = esI k r a) (by simp only [eI, esI, Fin.ext_iff]; omega),
          Matrix.one_apply_ne (by simp only [eI, Ne, Fin.ext_iff]; omega)]
        by_cases e : b = a
        · subst e
          have hn : nxt k r b = eI k r ⟨b.val + 1, h⟩ := rfl
          have := hc b
          simp only [if_true, κ, if_pos h, if_pos hn, smul_eq_mul]
          field_simp
          simp
        · simp [hba, e]
      · have hM : (M *ᵥ z) (eI k r b) = if b = a then κ a * (Γ⁻¹ *ᵥ z) (nxt k r a) else 0 := by
          simp only [mulVec, dotProduct, hent, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, hzS, mul_zero, sub_zero, hba]
          split_ifs
          · rw [Finset.mul_sum]; simp only [mul_assoc]
          · simp
        rw [dif_neg h, add_mulVec, one_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, hM,
          hzr _ (by simp only [eI]; omega) (rowE b)]
        by_cases e : b = a
        · subst e
          have n1 : nxt k r b = wI k r 0 := by simp only [wI, nxt, Fin.ext_iff, Fin.val_zero]; omega
          have n2 : wI k r 0 ≠ wI k r (Fin.last k) := by
            simp only [wI, Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega
          have hv : (Γ⁻¹ *ᵥ z) (nxt k r b) = ρ := by
            rw [hz, mulVec_smul, inv_mulVec_fix hΓu, n1]
            simp [bvec, n2]
          have := hc b
          have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
          simp only [if_true, κ, if_neg h, hv, smul_eq_mul]
          field_simp
          simp
        · simp [e]
    unfold PI.BesselMapUniq.psiGen
    simp only [hell, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.BmuRootVec
