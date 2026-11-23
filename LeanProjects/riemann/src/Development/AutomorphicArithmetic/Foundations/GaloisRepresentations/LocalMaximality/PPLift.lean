import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma smul_omB' {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  unfold omB at hy ⊢
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add z w _ _ hz hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hz hw
  | smul c z _ hz =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hz

private lemma rA_le_rB {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → F) (J : Finset (Fin (d + 1))) {h : F} (hh : h ∈ rA ℂ x J) :
    algebraMap F K h ∈ rB ℂ K x J := by
  unfold rB
  rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact (isIntegral_algebraMap : IsIntegral (rA ℂ x J) (algebraMap (rA ℂ x J) K ⟨h, hh⟩))

private lemma ratio_mem {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F)
    (I : Finset (Fin (d + 1))) (j : Fin (d + 1)) (N : ℕ) (T : Finset (Fin (d + 1))) (hT : T ⊆ I) :
    (∏ l ∈ T, x j / x l) ^ N ∈ rA ℂ x I := by
  unfold rA
  refine Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun l hl => ?_) N
  apply Algebra.subset_adjoin
  exact ⟨l, hT hl, j, rfl⟩

private theorem exteriorAlgebra_iota_mul_mem_omB_succ {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (a : ℕ)
    {p : Ω[K⁄ℂ]} (hp : p ∈ Submodule.span ℂ {m : Ω[K⁄ℂ] | ∃ c ∈ B, ∃ u ∈ B, m = c • D ℂ K u})
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B a) :
    ExteriorAlgebra.ι K p * y ∈ omB ℂ K B (a + 1) := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨c, hc, u, hu, rfl⟩ := hq
    unfold omB at hy ⊢
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨c * b, B.mul_mem hc hb, Fin.cons u v, ?_, ?_⟩
      · intro k
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa using hu
        · simpa using hv k
      · rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.vecTail,
          Function.comp_def, Fin.cons_succ, Fin.cons_zero]
        rw [mul_comm b c]
    | zero => simp
    | add z w _ _ hz hw =>
      rw [mul_add]
      exact Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hz
  | zero => simp
  | add q q' _ _ hq hq' =>
    rw [map_add, add_mul]
    exact Submodule.add_mem _ hq hq'
  | smul r q _ hq =>
    rw [LinearMap.map_smul_of_tower, smul_mul_assoc]
    exact Submodule.smul_mem _ r hq

private theorem iotaMulti_mem_omB_of_mem_span {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) :
    ∀ (a : ℕ) (m : Fin a → Ω[K⁄ℂ]),
      (∀ i, m i ∈ Submodule.span ℂ {m : Ω[K⁄ℂ] | ∃ c ∈ B, ∃ u ∈ B, m = c • D ℂ K u}) →
      ExteriorAlgebra.ιMulti K a m ∈ omB ℂ K B a := by
  intro a
  induction a with
  | zero =>
    intro m _
    unfold omB
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ a ih =>
    intro m hm
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact exteriorAlgebra_iota_mul_mem_omB_succ B a (hm 0) (ih _ fun i => hm i.succ)

private theorem pow_smul_D_mem_span_of_pow_mul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) {h v : K}
    (hh : h ∈ B) (N : ℕ) (hv : h ^ (N + 1) * v ∈ B) :
    h ^ (N + 2) • D ℂ K v ∈ Submodule.span ℂ {m : Ω[K⁄ℂ] | ∃ c ∈ B, ∃ u ∈ B, m = c • D ℂ K u} := by
  have key : h ^ (N + 2) • D ℂ K v =
      h • D ℂ K (h ^ (N + 1) * v) + (-((N + 1 : K) * (h ^ (N + 1) * v))) • D ℂ K h := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul K]
    module
  rw [key]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨h, hh, _, hv, rfl⟩)
    (Submodule.subset_span ⟨_, ?_, h, hh, rfl⟩)
  exact B.neg_mem (B.mul_mem (B.add_mem (B.natCast_mem N) B.one_mem) hv)

private theorem exists_pow_prod_ratio_mul_mem_rA_of_mem_union {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)
    (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hj : j ∈ J) :
    ∀ y ∈ rA ℂ (xv x) (I ∪ J), ∃ N : ℕ, (∏ l ∈ I, xv x l / xv x j) ^ N * y ∈ rA ℂ (xv x) J := by
  have hgen : ∀ l, xv x l / xv x j ∈ rA ℂ (xv x) J := fun l => Algebra.subset_adjoin ⟨j, hj, l, rfl⟩
  have hhA : (∏ l ∈ I, xv x l / xv x j) ∈ rA ℂ (xv x) J := Subalgebra.prod_mem _ fun l _ => hgen l
  intro y hy
  unfold rA at hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨i, hi, k, rfl⟩ := hz
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · refine ⟨1, ?_⟩
      rw [pow_one, ← Finset.mul_prod_erase I _ hiI]
      have h1 : xv x i ≠ 0 := (x i).ne_zero
      have h2 : xv x j ≠ 0 := (x j).ne_zero
      have he : xv x i / xv x j * (∏ l ∈ I.erase i, xv x l / xv x j) * (xv x k / xv x i) =
          (xv x k / xv x j) * ∏ l ∈ I.erase i, xv x l / xv x j := by
        field_simp
      rw [he]
      exact Subalgebra.mul_mem _ (hgen k) (Subalgebra.prod_mem _ fun l _ => hgen l)
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin ⟨i, hiJ, k, rfl⟩⟩
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₂, hN₂⟩ := h₂
    refine ⟨N₁ + N₂, ?_⟩
    have e : (∏ l ∈ I, xv x l / xv x j) ^ (N₁ + N₂) * (y₁ + y₂) =
        (∏ l ∈ I, xv x l / xv x j) ^ N₂ * ((∏ l ∈ I, xv x l / xv x j) ^ N₁ * y₁) +
          (∏ l ∈ I, xv x l / xv x j) ^ N₁ * ((∏ l ∈ I, xv x l / xv x j) ^ N₂ * y₂) := by
      ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hhA _) hN₁)
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hhA _) hN₂)
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₂, hN₂⟩ := h₂
    refine ⟨N₁ + N₂, ?_⟩
    have e : (∏ l ∈ I, xv x l / xv x j) ^ (N₁ + N₂) * (y₁ * y₂) =
        ((∏ l ∈ I, xv x l / xv x j) ^ N₁ * y₁) * ((∏ l ∈ I, xv x l / xv x j) ^ N₂ * y₂) := by
      ring
    rw [e]
    exact Subalgebra.mul_mem _ hN₁ hN₂

private theorem exists_isIntegral_pow_mul_of_isIntegral_of_denom {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra F K]
    (A A' : Subalgebra ℂ F) (s : F) (hs : s ∈ A') (hsA : s ∈ A)
    (hden : ∀ y ∈ A', ∃ N : ℕ, s ^ N * y ∈ A) {z : K} (hz : IsIntegral A' z) :
    ∃ N : ℕ, IsIntegral A (algebraMap F K (s ^ N) * z) := by
  obtain ⟨p, hpm, hpz⟩ := hz
  choose! f hf using fun i => hden _ (p.coeff i).2
  set M := ∑ i ∈ Finset.range (p.natDegree + 1), f i with hM
  have hcoef : ∀ i, s ^ M * (p.coeff i : F) ∈ A := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · have hle : f i ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      have e : s ^ M * (p.coeff i : F) = s ^ (M - f i) * (s ^ f i * (p.coeff i : F)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hsA _) (hf i)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      simp
  let t : A' := ⟨s ^ M, Subalgebra.pow_mem _ hs M⟩
  have hq : (p.scaleRoots t).eval₂ (algebraMap A' K) (algebraMap A' K t * z) = 0 :=
    Polynomial.scaleRoots_eval₂_eq_zero _ hpz
  have hlift : (p.scaleRoots t).map (algebraMap A' K) ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots]
    have hmem : ((p.coeff n * t ^ (p.natDegree - n) : A') : F) ∈ A := by
      rcases lt_or_ge n p.natDegree with hn | hn
      · obtain ⟨e, he⟩ : ∃ e, p.natDegree - n = e + 1 := ⟨p.natDegree - n - 1, by omega⟩
        rw [he]
        show (p.coeff n : F) * (s ^ M) ^ (e + 1) ∈ A
        have e2 : (p.coeff n : F) * (s ^ M) ^ (e + 1) = (s ^ M) ^ e * (s ^ M * (p.coeff n : F)) := by
          ring
        rw [e2]
        exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hsA _) _) (hcoef n)
      · rw [Nat.sub_eq_zero_of_le hn, pow_zero, mul_one]
        rcases eq_or_lt_of_le hn with h | h
        · rw [← h, hpm.coeff_natDegree]
          exact Subalgebra.one_mem _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
          exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (((Polynomial.monic_scaleRoots_iff t).mpr hpm).map _)
  refine ⟨M, q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap, ← Polynomial.eval₂_eq_eval_map]
  exact hq

private lemma split_form {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (a : ℕ) (hmono : ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a)
    (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hj : j ∈ J) (w : DR ℂ K)
    (hw : w ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) :
    ∃ g ∈ rA ℂ (xv x) I, ∃ w' ∈ omB ℂ K (rB ℂ K (xv x) J) a, w = algebraMap F K g • w' := by
  classical
  have hFA : (∏ l ∈ I, xv x l / xv x j) ∈ rA ℂ (xv x) J :=
    Subalgebra.prod_mem _ fun l _ => Algebra.subset_adjoin ⟨j, hj, l, rfl⟩
  have hFA' : (∏ l ∈ I, xv x l / xv x j) ∈ rA ℂ (xv x) (I ∪ J) :=
    Subalgebra.prod_mem _ fun l _ => Algebra.subset_adjoin ⟨j, Finset.mem_union_right _ hj, l, rfl⟩
  set hK : K := algebraMap F K (∏ l ∈ I, xv x l / xv x j) with hhK
  have hKB : hK ∈ rB ℂ K (xv x) J := rA_le_rB (xv x) J hFA
  have hden : ∀ z ∈ rB ℂ K (xv x) (I ∪ J), ∃ N : ℕ, hK ^ N * z ∈ rB ℂ K (xv x) J := by
    intro z hz
    unfold rB at hz
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hz
    obtain ⟨N, hN⟩ := exists_isIntegral_pow_mul_of_isIntegral_of_denom (rA ℂ (xv x) J) (rA ℂ (xv x) (I ∪ J)) _ hFA' hFA
      (exists_pow_prod_ratio_mul_mem_rA_of_mem_union x I J j hj) hz
    refine ⟨N, ?_⟩
    unfold rB
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff, hhK, ← map_pow]
    exact hN
  have hgen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a,
      ∃ E : ℕ, hK ^ E • y ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
    intro y hy
    unfold omB at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      obtain ⟨Nb, hNb⟩ := hden b hb
      choose f hf using fun k => hden (v k) (hv k)
      have hvk : ∀ k, hK ^ ((∑ k, f k) + 1) * v k ∈ rB ℂ K (xv x) J := by
        intro k
        have hle : f k ≤ (∑ k, f k) + 1 :=
          le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)) (Nat.le_succ _)
        rw [show hK ^ ((∑ k, f k) + 1) * v k = hK ^ ((∑ k, f k) + 1 - f k) * (hK ^ f k * v k) by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]]
        exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hKB _) (hf k)
      refine ⟨Nb + ((∑ k, f k) + 2) * a, ?_⟩
      have hmul : (ExteriorAlgebra.ιMulti K a fun k => hK ^ ((∑ k, f k) + 2) • D ℂ K (v k)) =
          hK ^ (((∑ k, f k) + 2) * a) • ExteriorAlgebra.ιMulti K a (fun k => D ℂ K (v k)) := by
        have := (ExteriorAlgebra.ιMulti K a).toMultilinearMap.map_smul_univ
          (fun _ => hK ^ ((∑ k, f k) + 2)) (fun k => D ℂ K (v k))
        simpa [Finset.prod_const, pow_mul] using this
      have e : hK ^ (Nb + ((∑ k, f k) + 2) * a) • (b • ExteriorAlgebra.ιMulti K a fun k => D ℂ K (v k)) =
          (hK ^ Nb * b) • ExteriorAlgebra.ιMulti K a (fun k => hK ^ ((∑ k, f k) + 2) • D ℂ K (v k)) := by
        rw [hmul, smul_smul, smul_smul, pow_add]
        congr 1
        ring
      rw [e]
      exact smul_omB' _ a hNb
        (iotaMulti_mem_omB_of_mem_span _ a _ fun k => pow_smul_D_mem_span_of_pow_mul_mem _ hKB (∑ k, f k) (hvk k))
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨E₁, hE₁⟩ := h₁
      obtain ⟨E₂, hE₂⟩ := h₂
      refine ⟨E₁ + E₂, ?_⟩
      have e1 : hK ^ (E₁ + E₂) • y₁ = hK ^ E₂ • (hK ^ E₁ • y₁) := by
        rw [smul_smul, ← pow_add, add_comm]
      have e2 : hK ^ (E₁ + E₂) • y₂ = hK ^ E₁ • (hK ^ E₂ • y₂) := by
        rw [smul_smul, ← pow_add]
      rw [smul_add, e1, e2]
      exact Submodule.add_mem _ (smul_omB' _ a (Subalgebra.pow_mem _ hKB _) hE₁)
        (smul_omB' _ a (Subalgebra.pow_mem _ hKB _) hE₂)
    | smul r y _ h =>
      obtain ⟨E, hE⟩ := h
      exact ⟨E, by rw [smul_comm]; exact Submodule.smul_mem _ r hE⟩
  obtain ⟨E, hE⟩ := hgen w hw
  refine ⟨(∏ l ∈ I, xv x j / xv x l) ^ E, ratio_mem (xv x) I j E I (subset_refl _), hK ^ E • w, hE, ?_⟩
  have hone : algebraMap F K ((∏ l ∈ I, xv x j / xv x l) ^ E) * hK ^ E = 1 := by
    rw [hhK, ← map_pow, ← map_mul, ← mul_pow, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one (fun l _ => ?_), one_pow, map_one]
    have h1 : xv x l ≠ 0 := (x l).ne_zero
    have h2 : xv x j ≠ 0 := (x j).ne_zero
    field_simp
  rw [smul_smul, hone, one_smul]

private lemma wd_act {S E κ : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] [LinearOrder κ]
    (act : S →ₐ[ℂ] Module.End ℂ E) (z : κ → S) (f : Finset κ → S) (m : E) (t : Finset κ) :
    wd (fun l => act (z l)) (fun L => act (f L) m) t = act (wd (fun l => Algebra.lmul ℂ S (z l)) f t) m := by
  simp only [wd, LinearMap.pi_apply, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul, Module.End.mul_apply]

private lemma mulP_tmul {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    (f : F) (v : DR ℂ K) : mulP F K (f ⊗ₜ[ℂ] v) = algebraMap F K f • v := by
  simp [mulP]

private lemma omG_mul {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i : Fin (d + 1)) :
    omG x i * (x i : F) ^ d = ∏ m ∈ ({i}ᶜ : Finset (Fin (d + 1))), (x m : F) := by
  have hx : ((x i : Fˣ) : F) ≠ 0 := (x i).ne_zero
  unfold omG
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.prod_eq_prod_compl_mul i]
  field_simp
  ring

private lemma col_cycle (hMu : ThMu) (hMuLat : ThMuLat) (hWd : WdUni) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (hP : T.Good) (I J : Finset (Fin (d + 1))) (hI : I.Nonempty)
    (hJ : J.Nonempty) (hi : pk I ∈ I) (hj : pk J ∈ J) (m : E) (hm : m ∈ T.M I J) (c : S)
    (hc : c * ∏ l ∈ ({pk I}ᶜ : Finset (Fin (d + 1))), (T.X l : S) = (T.X (pk I) : S) ^ d) :
    (fun L => T.act (detC T.rowMu (uni {pk I} L)) (T.act c m)) ∈ (T.colCx n11 T.mu I J).Z d := by
  obtain ⟨-, hLat⟩ := hMuLat d S E T hP
  obtain ⟨hwd0, hempty, -, -⟩ := hMu d S E T
  have hcard : ∀ L : Finset (Mi d), (uni ({pk I} : Finset (Fin (d + 1))) L).card = 1 + L.card := by
    intro L
    simp [uni, Finset.card_disjSum]
  unfold Cx.Z Sys.colCx kosT acx
  rw [Submodule.mem_inf]
  constructor
  · simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
    intro L
    split_ifs with hL
    · have hLc : L.card = d := by exact_mod_cast hL
      obtain ⟨s, hs, hdet⟩ := hLat {pk I} J L (Finset.singleton_nonempty _) (pk J) hj
      have hs' : s ∈ T.R I J :=
        hP.monoR {pk I} I J J (Finset.singleton_nonempty _) hJ (Finset.singleton_subset_iff.2 hi)
          le_rfl hs
      have key : ((∏ l ∈ L, T.u n11 (pk I) (pk J) l : Sˣ) : S) * s =
          detC T.rowMu (uni {pk I} L) * c := by
        rw [hdet, Units.coe_prod]
        simp only [Sys.u, n11, pow_one, Units.val_mul, Finset.prod_const, hLc]
        linear_combination (-(s * (T.Y (pk J) : S) ^ d)) * hc
      refine ⟨T.act s m, hP.stab I J hI hJ s hs' m hm, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, key, map_mul, Module.End.mul_apply]
    · have hL' : L.card ≠ d := fun h => hL (by rw [h])
      have h0 : detC T.rowMu (uni {pk I} L) = 0 := by
        unfold detC
        rw [dif_neg]
        rw [hcard]
        omega
      rw [h0, map_zero]
      simp
  · rw [LinearMap.mem_ker]
    funext t
    rw [wd_act]
    have h1 := congrFun hwd0 (uni {pk I} t)
    rw [(hWd _ _ _ _ _ _ _).1] at h1
    have h2 : (wd fun l => Algebra.lmul ℂ S (T.mu l)) (fun L => detC T.rowMu (uni {pk I} L)) t = 0 := by
      simpa [wd, app, inrE, hempty] using h1
    rw [h2, map_zero]
    rfl

theorem UpperTheory.Gal.productCup_of_system.pLift_of :
    ThMu → ThMuLat → KapInd → ActsLin → LatA → GoodZ → SysOk → WdUni → PLift := by
  intro hMu hMuLat hKap hActs hLat hGood hSys hWd F K _ _ _ _ _ _ d x hcov a I J hI hJ w hw
  have hi : pk I ∈ I := by
    unfold pk
    rw [dif_pos hI]
    exact Finset.min'_mem I hI
  have hj : pk J ∈ J := by
    unfold pk
    rw [dif_pos hJ]
    exact Finset.min'_mem J hJ
  obtain ⟨-, hPg, hmono⟩ := hGood F K d x hcov a
  obtain ⟨g, hg, w', hw', rfl⟩ := split_form x hcov a hmono I J (pk J) hj w hw
  obtain ⟨τ, hτ⟩ := hcov.exists_isTop
  obtain ⟨-, -, -, -, hmulP, -⟩ := hActs F K d x hcov τ hτ a
  obtain ⟨-, hom, -⟩ := hLat F d x hcov.pd I (pk I) hi
  have hG : omG x (pk I) ≠ 0 := by
    unfold omG
    exact Finset.prod_ne_zero_iff.mpr fun l _ => div_ne_zero (x l).ne_zero (x _).ne_zero
  have hm : (omG x (pk I) * g) ⊗ₜ[ℂ] w' ∈ (sysP K x a).M I J := by
    apply Submodule.apply_mem_map₂ _ ?_ hw'
    rw [hom, mul_div_cancel_left₀ _ hG]
    exact hg
  have e : ∀ l, ((sysP K x a).X l : F ⊗[ℂ] K) = Algebra.TensorProduct.includeLeftRingHom (x l : F) :=
    fun l => rfl
  have hc' : ((omG x (pk I))⁻¹ ⊗ₜ[ℂ] (1 : K)) * ∏ l ∈ ({pk I}ᶜ : Finset (Fin (d + 1))), ((sysP K x a).X l : F ⊗[ℂ] K)
      = ((sysP K x a).X (pk I) : F ⊗[ℂ] K) ^ d := by
    simp only [e, ← map_prod, ← map_pow]
    rw [show (omG x (pk I))⁻¹ ⊗ₜ[ℂ] (1 : K) = Algebra.TensorProduct.includeLeftRingHom (omG x (pk I))⁻¹ from rfl,
      ← map_mul, ← omG_mul x (pk I), ← mul_assoc, inv_mul_cancel₀ hG, one_mul]
  refine ⟨_, col_cycle hMu hMuLat hWd (sysP K x a) hPg I J hI hJ hi hj _ hm _ hc', ?_⟩
  intro L hL
  rw [hmulP, hmulP, mulP_tmul]
  rw [hKap F K d x hcov _ _ (sysP K x a)
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K))
    (fun i => by simp [sysP]) (fun i => by simp [sysP]) (pk I) L hL]
  simp only [Algebra.TensorProduct.productMap_apply_tmul, IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq,
    mul_one, smul_smul, ← map_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hG, one_mul]
