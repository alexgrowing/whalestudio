import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

section FrameOfGens

variable {K : Type} [Field K] {N : ℕ}

theorem det_mem_of_mem_matrix {R : Subring K} {A : Matrix (Fin N) (Fin N) K} (h : A ∈ R.matrix) : A.det ∈ R := by
  let A' : Matrix (Fin N) (Fin N) R := fun i j => ⟨A i j, h i j⟩
  have e : A = R.subtype.mapMatrix A' := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (A'.det).2

theorem adjugate_mem_of_mem_matrix {R : Subring K} {A : Matrix (Fin N) (Fin N) K} (h : A ∈ R.matrix) :
    A.adjugate ∈ R.matrix := by
  let A' : Matrix (Fin N) (Fin N) R := fun i j => ⟨A i j, h i j⟩
  have e : A = R.subtype.mapMatrix A' := by ext i j; rfl
  rw [e, ← RingHom.map_adjugate]
  intro i j
  exact (A'.adjugate i j).2

theorem prod_castSucc_div_succ_eq : ∀ (n : ℕ) (f : Fin (n + 1) → K), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.castSucc / f i.succ = f 0 / f (Fin.last n)
  | 0, f, hf => by simp [div_self (hf 0)]
  | n + 1, f, hf => by
    have ih := prod_castSucc_div_succ_eq n (fun i => f i.castSucc) (fun i => hf _)
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih, Fin.castSucc_zero, Fin.succ_last]
    have h1 := hf (Fin.last n).castSucc
    have h2 := hf (Fin.last (n + 1))
    field_simp

theorem frame_of_content_gens : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (M : Matrix (Fin N) (Fin N) K) (j : Fin N) (γ : K) (η : Fin (N + 1) → K), Fr R M → γ ∈ R → γ ≠ 0 → (∀ i, Gen R (gens γ (fun l => M⁻¹ l j) i) (η i)) → (∃ B : Matrix (Fin N) (Fin N) K, B.BlockTriangular id ∧ Fr R (dg j γ * M * B) ∧ ∀ i, B i i = η i.castSucc / η i.succ) ∧ (η 0)⁻¹ ∈ R ∧ η (Fin.last N) / γ ∈ R ∧ (∀ i, η i ∈ R ∧ γ / η i ∈ R) ∧ ∀ i : Fin N, η i.succ / η i.castSucc ∈ R ∧ ∃ α ∈ R, ∃ β ∈ R, η i.castSucc = α * M⁻¹ i j + β * η i.succ := by
  intro K _ N R M j γ η hM hγ hγ0 hG
  set y : Fin N → K := fun l => M⁻¹ l j with hy
  have hdetU : IsUnit M.det := isUnit_iff_ne_zero.2 hM.1
  have hyR : ∀ l, y l ∈ R := fun l => hM.2.2 l j
  have hη0 : ∀ i, η i ≠ 0 := fun i => (hG i).1
  have hdiv : ∀ i s, gens γ y i s / η i ∈ R := fun i s => (hG i).2.1 s
  have hgR : ∀ i s, gens γ y i s ∈ R := by
    intro i s
    cases s with
    | none => exact hγ
    | some k =>
      simp only [gens, Option.elim]
      split_ifs
      · exact hyR k
      · exact R.zero_mem
  have hηR : ∀ i, η i ∈ R := by
    intro i
    obtain ⟨α, hα, he⟩ := (hG i).2.2
    rw [he]
    exact R.sum_mem fun s _ => R.mul_mem (hα s) (hgR i s)
  have hγη : ∀ i, γ / η i ∈ R := fun i => hdiv i none
  have hyη : ∀ (i : Fin (N + 1)) (k : Fin N), (i : ℕ) ≤ k → y k / η i ∈ R := by
    intro i k hk
    have := hdiv i (some k)
    simpa [gens, hk] using this
  have hinv0 : (η 0)⁻¹ ∈ R := by
    have h1 : ∑ l, M j l * y l = 1 := by
      have := congrFun (congrFun (Matrix.mul_nonsing_inv M hdetU) j) j
      simpa [Matrix.mul_apply] using this
    have e : (η 0)⁻¹ = ∑ l, M j l * (y l / η 0) := by
      rw [inv_eq_one_div, ← h1, Finset.sum_div]
      simp only [mul_div_assoc]
    rw [e]
    exact R.sum_mem fun l _ => R.mul_mem (hM.2.1 j l) (hyη 0 l (Nat.zero_le _))
  have hlast : η (Fin.last N) / γ ∈ R := by
    obtain ⟨α, hα, he⟩ := (hG (Fin.last N)).2.2
    have hk : ∀ k : Fin N, ¬ (N ≤ (k : ℕ)) := fun k => not_le.2 k.2
    have e : η (Fin.last N) = α none * γ := by
      rw [he, Fintype.sum_option]
      simp [gens, hk]
    rw [e, mul_div_assoc, div_self hγ0, mul_one]
    exact hα none
  have hsplit : ∀ (i : Fin N) s, gens γ y i.castSucc s = gens γ y i.succ s + (if s = some i then y i else 0) := by
    intro i s
    cases s with
    | none => simp [gens]
    | some k =>
      simp only [gens, Option.elim, Fin.coe_castSucc, Fin.val_succ, Option.some.injEq]
      by_cases h : k = i
      · subst h; simp
      · have : (k : ℕ) ≠ i := fun e => h (Fin.ext e)
        by_cases h2 : (i : ℕ) ≤ k
        · rw [if_pos h2, if_pos (by omega), if_neg h, add_zero]
        · rw [if_neg h2, if_neg (by omega), if_neg h, add_zero]
  have hstep : ∀ i : Fin N, η i.succ / η i.castSucc ∈ R ∧
      ∃ α ∈ R, ∃ β ∈ R, η i.castSucc = α * y i + β * η i.succ := by
    intro i
    constructor
    · obtain ⟨α, hα, he⟩ := (hG i.succ).2.2
      rw [he, Finset.sum_div]
      refine R.sum_mem fun s _ => ?_
      rw [mul_div_assoc]
      refine R.mul_mem (hα s) ?_
      by_cases hs : s = some i
      · subst hs; simp [gens]
      · have := hdiv i.castSucc s
        rwa [hsplit i s, if_neg hs, add_zero] at this
    · obtain ⟨α, hα, he⟩ := (hG i.castSucc).2.2
      refine ⟨α (some i), hα _, ∑ s, α s * (gens γ y i.succ s / η i.succ),
        R.sum_mem fun s _ => R.mul_mem (hα s) (hdiv _ s), ?_⟩
      rw [he, Finset.sum_mul]
      simp_rw [hsplit i, mul_add]
      rw [Finset.sum_add_distrib]
      have h2 : ∑ s, α s * (if s = some i then y i else 0) = α (some i) * y i := by
        simp [mul_ite]
      rw [h2, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, div_mul_cancel₀ _ (hη0 _)]
  choose hq α hα β hβ heq using hstep
  refine ⟨?_, hinv0, hlast, fun i => ⟨hηR i, hγη i⟩, fun i => ⟨hq i, α i, hα i, β i, hβ i, heq i⟩⟩
  let w : Fin N → Fin N → K := fun i k => if i < k then y k / η i.succ else 0
  have hwR : ∀ i k, w i k ∈ R := by
    intro i k
    simp only [w]
    split_ifs with h
    · exact hyη _ _ (by rw [Fin.lt_def] at h; simp only [Fin.val_succ]; omega)
    · exact R.zero_mem
  let B : Matrix (Fin N) (Fin N) K := fun k i =>
    α i * (if k ≤ i then y k / η i.succ else 0) + (if k = i then β i else 0)
  have hBt : B.BlockTriangular id := by
    intro k i hik
    simp only [id] at hik
    simp [B, not_le.2 hik, ne_of_gt hik]
  have hBd : ∀ i, B i i = η i.castSucc / η i.succ := by
    intro i
    simp only [B, le_refl, if_true]
    rw [heq i, add_div, mul_div_assoc, mul_div_cancel_right₀ _ (hη0 _)]
  have hMB : ∀ r i, (M * B) r i =
      α i * ((1 : Matrix (Fin N) (Fin N) K) r j / η i.succ - ∑ k, M r k * w i k) + β i * M r i := by
    intro r i
    have h1 : ∑ k, M r k * y k = (1 : Matrix (Fin N) (Fin N) K) r j := by
      rw [← Matrix.mul_nonsing_inv M hdetU, Matrix.mul_apply]
    have hv : ∀ k, (if k ≤ i then y k / η i.succ else 0) = y k / η i.succ - w i k := by
      intro k
      simp only [w]
      by_cases h : k ≤ i
      · rw [if_pos h, if_neg (not_lt.2 h), sub_zero]
      · rw [if_neg h, if_pos (not_le.1 h), sub_self]
    rw [Matrix.mul_apply]
    simp only [B, hv]
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← h1, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · ring
  have hdR : ∀ r, Function.update (1 : Fin N → K) j γ r ∈ R := by
    intro r
    by_cases h : r = j
    · subst h; simpa using hγ
    · simp [h, R.one_mem]
  have hAR : dg j γ * M * B ∈ R.matrix := by
    intro r i
    simp only [dg, Matrix.mul_assoc, Matrix.diagonal_mul, hMB]
    have e : Function.update (1 : Fin N → K) j γ r * ((1 : Matrix (Fin N) (Fin N) K) r j / η i.succ) ∈ R := by
      by_cases h : r = j
      · subst h; simpa [div_eq_mul_inv] using hγη i.succ
      · simp [Matrix.one_apply_ne h]
    have e2 : ∀ d a s m : K, d * (α i * (a / η i.succ - s) + β i * m) =
        α i * (d * (a / η i.succ)) - d * α i * s + d * β i * m := by intros; ring
    rw [e2]
    exact R.add_mem (R.sub_mem (R.mul_mem (hα i) e) (R.mul_mem (R.mul_mem (hdR r) (hα i))
      (R.sum_mem fun k _ => R.mul_mem (hM.2.1 r k) (hwR i k)))) (R.mul_mem (R.mul_mem (hdR r) (hβ i)) (hM.2.1 r i))
  have htel := prod_castSucc_div_succ_eq N η hη0
  have hdetA : (dg j γ * M * B).det = γ * M.det * (η 0 / η (Fin.last N)) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_of_upperTriangular hBt, dg, Matrix.det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ j)]
    simp [hBd, htel]
  have hdetA0 : (dg j γ * M * B).det ≠ 0 := by
    rw [hdetA]
    exact mul_ne_zero (mul_ne_zero hγ0 hM.1) (div_ne_zero (hη0 0) (hη0 _))
  have hdetinv : ((dg j γ * M * B).det)⁻¹ ∈ R := by
    have e : ((dg j γ * M * B).det)⁻¹ = (η (Fin.last N) / γ) * (M⁻¹).det * (η 0)⁻¹ := by
      rw [hdetA, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      have := hη0 0
      have := hη0 (Fin.last N)
      have := hM.1
      field_simp
    rw [e]
    exact R.mul_mem (R.mul_mem hlast (det_mem_of_mem_matrix hM.2.2)) hinv0
  refine ⟨B, hBt, ⟨hdetA0, hAR, ?_⟩, hBd⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  intro r i
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact R.mul_mem hdetinv (adjugate_mem_of_mem_matrix hAR r i)

end FrameOfGens

end GlobalTheory.LatChain
