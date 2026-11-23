import Mathlib
import Formalism.PeriodIntegrals.LatCountG

open Matrix
open scoped ENNReal

noncomputable section

namespace PI.MultFromLatWork

open Formalism.REAL

lemma kset_unitary {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk'.1,
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk'.1⟩

lemma kset_conjTranspose {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  obtain ⟨h1, h2⟩ := kset_unitary hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact h1
  · calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hk'.2]
      _ = (kᴴ * k) * Jm ε * kᴴ := by simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]

lemma hs_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma inP_conj {n : ℕ} {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X) : inP ε (k * X * kᴴ) := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkh : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Jm ε = Jm ε * kᴴ := kset_conjTranspose hk
  have hJkh := hkh.2
  have hJk := hk'.2
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hX2 : X * Jm ε = -(Jm ε * X) := hX.2
  have e1 : (k * X * kᴴ)ᴴ * Jm ε = k * (Xᴴ * Jm ε) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hJkh]
  have e2 : Jm ε * (k * X * kᴴ) = k * (Jm ε * X) * kᴴ := by
    calc Jm ε * (k * X * kᴴ) = (Jm ε * k) * X * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (k * Jm ε) * X * kᴴ := by rw [← hJk]
      _ = k * (Jm ε * X) * kᴴ := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · show (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = 0
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hG, Matrix.mul_zero, Matrix.zero_mul]
  · calc k * X * kᴴ * Jm ε = k * (X * Jm ε) * kᴴ := by simp only [Matrix.mul_assoc, hJkh]
      _ = k * (-(Jm ε * X)) * kᴴ := by rw [hX2]
      _ = -(k * (Jm ε * X) * kᴴ) := by rw [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(Jm ε * (k * X * kᴴ)) := by rw [e2]

lemma hs_conj {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk1 : kᴴ * k = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (k * X * kᴴ) = hs X := by
  rw [hs_eq_trace, hs_eq_trace]
  congr 1
  have e : (k * X * kᴴ)ᴴ * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hk1, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk1, Matrix.one_mul]

lemma symD_set_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) :
    {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε ∧ inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (hs X)} ⊆
    {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε ∧ inP ε X ∧
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        k * NormedSpace.exp X ∧ t = Real.sqrt (hs X)} := by
  rintro t ⟨k, X, hk, hX, hg, rfl⟩
  obtain ⟨h1, h2⟩ := kset_unitary hk
  have hku : IsUnit k := ⟨⟨k, kᴴ, h2, h1⟩, rfl⟩
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hX2 : X * Jm ε = -(Jm ε * X) := hX.2
  have hnX : inP ε (-X) := by
    refine ⟨?_, ?_⟩
    · show (-X)ᴴ * Jm ε + Jm ε * (-X) = 0
      rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hG, neg_zero]
    · show -X * Jm ε = -(Jm ε * -X)
      rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hX2, neg_neg]
  refine ⟨kᴴ, k * -X * kᴴ, kset_conjTranspose hk, inP_conj hk hnX, ?_, ?_⟩
  · have hexp : NormedSpace.exp (k * -X * kᴴ) = k * NormedSpace.exp (-X) * kᴴ := by
      rw [← hkinv]
      exact Matrix.exp_conj k (-X) hku
    have hEE : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
      rw [← Matrix.exp_add_of_commute X (-X) (Commute.neg_right (Commute.refl X)), add_neg_cancel,
        NormedSpace.exp_zero]
    show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ) = _
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hg, hexp]
    calc k * NormedSpace.exp X * (kᴴ * (k * NormedSpace.exp (-X) * kᴴ)) =
        k * (NormedSpace.exp X * ((kᴴ * k) * NormedSpace.exp (-X))) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.one_mul, hEE, Matrix.mul_one, h2]
  · rw [hs_conj h1]
    congr 1
    simp [hs, norm_neg]

theorem symD_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : PI.symD ε g⁻¹ = PI.symD ε g := by
  unfold PI.symD
  congr 1
  apply Set.Subset.antisymm
  · simpa only [inv_inv] using symD_set_inv g⁻¹
  · exact symD_set_inv g

lemma encard_le_of_finset {α : Type*} (T : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (↑s : Set α) ⊆ T → (s.card : ℝ) ≤ B) :
    ((T.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal B := by
  by_cases hT : T.Finite
  · have hs := h hT.toFinset (by simp)
    rw [hT.encard_eq_coe_toFinset_card]
    simp only [ENat.toENNReal_coe]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hs
  · exfalso
    obtain ⟨t, ht, hc⟩ := Set.Infinite.exists_subset_card_eq hT (⌈B⌉₊ + 1)
    have h1 := h t ht
    rw [hc] at h1
    push_cast at h1
    have h2 := Nat.le_ceil B
    linarith

lemma const_eq (I : Formalism.MainNotions.S.AutInst) (r : NumberField.InfinitePlace I.F → ℝ) (t : ℝ) :
    (3 * Real.sqrt (I.n : ℝ) / (t * t)) ^ (2 * I.n ^ 2 * I.f) *
        Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, (2 * r v)) =
      PI.LatCountG.COm I r / t ^ (4 * I.n ^ 2 * I.f) := by
  have he : ∑ v, (2 * r v) = 2 * ∑ v, r v := by rw [Finset.mul_sum]
  have hp : t ^ (4 * I.n ^ 2 * I.f) = (t * t) ^ (2 * I.n ^ 2 * I.f) := by ring
  have hx : 2 * (I.n : ℝ) ^ 2 * (2 * ∑ v, r v) = 4 * (I.n : ℝ) ^ 2 * ∑ v, r v := by ring
  rw [PI.LatCountG.COm, hp, he, hx, div_pow]
  ring

theorem multBound_of (hS : PI.SymDist) (I : Formalism.MainNotions.S.AutInst) (hL : PI.LatCountG.LatCount I) :
    PI.LatCountG.MultBound I := by
  intro r hr K' hK' x hx
  unfold Formalism.L2.SG.FoldBound.mult
  refine iSup_le fun y => ?_
  by_cases hne : ({γ : Formalism.MainNotions.LeviCoordinates.rr_GF I |
      x⁻¹ * ((γ : I.GA) * y) ∈ PI.LatCountG.Om I r (K' : Set I.Gf)} : Set _).Nonempty
  · obtain ⟨γ0, hγ0⟩ := hne
    apply encard_le_of_finset
    intro s hs
    let f : Formalism.MainNotions.LeviCoordinates.rr_GF I → I.GFset := fun γ =>
      ⟨(γ : I.GA) * (γ0 : I.GA)⁻¹,
        (Formalism.MainNotions.LeviCoordinates.rr_GF I).mul_mem γ.2 ((Formalism.MainNotions.LeviCoordinates.rr_GF I).inv_mem γ0.2)⟩
    have finj : Function.Injective f := by
      intro a b hab
      have hv : (a : I.GA) * (γ0 : I.GA)⁻¹ = (b : I.GA) * (γ0 : I.GA)⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_right_cancel hv)
    have hcount := hL x x hx hx (fun v => 2 * r v) (fun v => by linarith [hr v])
      (s.map ⟨f, finj⟩) ?_
    · calc (s.card : ℝ) = ((s.map ⟨f, finj⟩).card : ℝ) := by rw [Finset.card_map]
        _ ≤ _ := hcount
        _ = _ := const_eq I r (PI.LatCountG.tau1 I x)
    · intro γ' hγ'
      rw [Finset.mem_map] at hγ'
      obtain ⟨γ, hγs, rfl⟩ := hγ'
      have hγ : x⁻¹ * ((γ : I.GA) * y) ∈ PI.LatCountG.Om I r (K' : Set I.Gf) := hs hγs
      have hid : x⁻¹ * ((γ : I.GA) * (γ0 : I.GA)⁻¹) * x =
          (x⁻¹ * ((γ : I.GA) * y)) * (x⁻¹ * ((γ0 : I.GA) * y))⁻¹ := by group
      show (x⁻¹ * ((γ : I.GA) * (γ0 : I.GA)⁻¹) * x).2 ∈ I.Kset ∧
        ∀ v, PI.symD (I.ε v) ((x⁻¹ * ((γ : I.GA) * (γ0 : I.GA)⁻¹) * x).1 v) ≤ 2 * r v
      rw [hid]
      obtain ⟨h1, h2⟩ := hγ
      obtain ⟨h1', h2'⟩ := hγ0
      refine ⟨hK' ?_, fun v => ?_⟩
      · simp only [Prod.snd_mul, Prod.snd_inv]
        exact K'.mul_mem h2 (K'.inv_mem h2')
      · simp only [Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply]
        calc PI.symD (I.ε v) ((x⁻¹ * ((γ : I.GA) * y)).1 v * ((x⁻¹ * ((γ0 : I.GA) * y)).1 v)⁻¹) ≤
            PI.symD (I.ε v) ((x⁻¹ * ((γ : I.GA) * y)).1 v) +
              PI.symD (I.ε v) (((x⁻¹ * ((γ0 : I.GA) * y)).1 v)⁻¹) := hS _ _ _ _
          _ = PI.symD (I.ε v) ((x⁻¹ * ((γ : I.GA) * y)).1 v) +
              PI.symD (I.ε v) ((x⁻¹ * ((γ0 : I.GA) * y)).1 v) := by rw [symD_inv]
          _ ≤ r v + r v := add_le_add (h1 v) (h1' v)
          _ = 2 * r v := by ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem multFromLat_main : PI.LatCountG.MultFromLat := fun hS I hL => multBound_of hS I hL

end PI.MultFromLatWork

end
