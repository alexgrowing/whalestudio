import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrEll.RealClasses

section Mat

variable {r : ℕ}

theorem form_diagonal (d : Fin r → ℝ) (u : Fin r → ℂ) :
    star u ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ u) = ((∑ i, d i * Complex.normSq (u i) : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl

private lemma eq_zero_of_sum_weighted_normSq_nonpos {r : ℕ} (x : Fin r → ℝ) (w : Fin r → ℂ) (hw : ∀ k, ¬ 0 < x k → w k = 0)
    (hs : ∑ k, x k * Complex.normSq (w k) ≤ 0) : w = 0 := by
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ x k * Complex.normSq (w k) := by
    intro k _
    by_cases hk : 0 < x k
    · exact mul_nonneg hk.le (Complex.normSq_nonneg _)
    · rw [hw k hk, map_zero, mul_zero]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hs (Finset.sum_nonneg hnn))
  funext k
  by_cases hk : 0 < x k
  · rcases mul_eq_zero.1 (hz k (Finset.mem_univ k)) with h0 | h0
    · exact absurd h0 hk.ne'
    · exact Complex.normSq_eq_zero.1 h0
  · exact hw k hk

private lemma eq_zero_of_mem_span_single_of_not {r : ℕ} (p : Fin r → Prop) (w : Fin r → ℂ)
    (hw : w ∈ Submodule.span ℂ (Set.range fun i : {i // p i} => (Pi.single i.1 1 : Fin r → ℂ))) :
    ∀ k, ¬ p k → w k = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro k hk
    have hne : k ≠ i.1 := fun h => hk (by rw [h]; exact i.2)
    simp [Pi.single_apply, hne]
  | zero => intro k _; rfl
  | add y z _ _ hy hz => intro k hk; simp [hy k hk, hz k hk]
  | smul a y _ hy => intro k hk; simp [hy k hk]

theorem card_pos_le (d x : Fin r → ℝ) (N : Matrix (Fin r) (Fin r) ℂ)
    (h : Nᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * N = Matrix.diagonal fun i => (x i : ℂ)) :
    Fintype.card {i // 0 < x i} ≤ Fintype.card {i // 0 < d i} := by
  classical
  have key : ∀ w : Fin r → ℂ, ∑ k, d k * Complex.normSq ((N *ᵥ w) k) = ∑ k, x k * Complex.normSq (w k) := by
    intro w
    have e1 := form_diagonal d (N *ᵥ w)
    have e2 := form_diagonal x w
    have e3 : star (N *ᵥ w) ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ (N *ᵥ w)) =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (x i : ℂ)) *ᵥ w) := by
      rw [← h]
      simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
    exact_mod_cast e1.symm.trans (e3.trans e2)
  have li : ∀ p : Fin r → Prop, LinearIndependent ℂ (fun i : {i // p i} => (Pi.single i.1 1 : Fin r → ℂ)) := by
    intro p
    have := (Pi.basisFun ℂ (Fin r)).linearIndependent.comp (Subtype.val : {i // p i} → Fin r) Subtype.val_injective
    simpa [Function.comp_def] using this
  have hv : LinearIndependent ℂ (Matrix.mulVecLin N ∘ fun i : {i // 0 < x i} => (Pi.single i.1 1 : Fin r → ℂ)) := by
    refine (li _).map ?_
    rw [Submodule.disjoint_def]
    intro w hw hk
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
    refine eq_zero_of_sum_weighted_normSq_nonpos x w (eq_zero_of_mem_span_single_of_not _ w hw) ?_
    rw [← key, hk]
    simp
  have hvw : Disjoint (Submodule.span ℂ (Set.range (Matrix.mulVecLin N ∘ fun i : {i // 0 < x i} => (Pi.single i.1 1 : Fin r → ℂ))))
      (Submodule.span ℂ (Set.range fun j : {j // ¬ 0 < d j} => (Pi.single j.1 1 : Fin r → ℂ))) := by
    rw [Submodule.disjoint_def]
    intro z hz1 hz2
    rw [Set.range_comp, Submodule.span_image, Submodule.mem_map] at hz1
    obtain ⟨w, hw, rfl⟩ := hz1
    have hsupp := eq_zero_of_mem_span_single_of_not _ _ hz2
    rw [Matrix.mulVecLin_apply] at hsupp ⊢
    have hle : ∑ k, d k * Complex.normSq ((N *ᵥ w) k) ≤ 0 := by
      refine Finset.sum_nonpos fun k _ => ?_
      by_cases hk : 0 < d k
      · rw [hsupp k (not_not.2 hk), map_zero, mul_zero]
      · exact mul_nonpos_iff.2 (Or.inr ⟨not_lt.1 hk, Complex.normSq_nonneg _⟩)
    rw [key] at hle
    rw [eq_zero_of_sum_weighted_normSq_nonpos x w (eq_zero_of_mem_span_single_of_not _ w hw) hle, Matrix.mulVec_zero]
  have hli := LinearIndependent.sum_type hv (li fun j => ¬ 0 < d j) hvw
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_sum, Module.finrank_fin_fun] at hc
  have h1 := Fintype.card_subtype_compl (fun j => 0 < d j)
  have h2 := Fintype.card_subtype_le (fun j => 0 < d j)
  simp only [Fintype.card_fin] at h1 h2
  omega

theorem exists_perm (ε : Fin r → Bool) (x : Fin r → ℝ) (hx : ∀ i, x i ≠ 0) (N : Matrix (Fin r) (Fin r) ℂ)
    (h : Nᴴ * Formalism.REAL.Jm ε * N = Matrix.diagonal fun i => (x i : ℂ)) :
    ∃ y : Equiv.Perm (Fin r), ε ∘ y = fun i => decide (0 < x i) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Fin r → ℝ, s = fun i => if ε i then 1 else -1 := ⟨_, rfl⟩
  have hsε : ∀ j, 0 < s j ↔ ε j = true := by
    intro j; cases hj : ε j <;> simp [hs, hj]
  have hs0 : ∀ j, s j ≠ 0 := by
    intro j; cases hj : ε j <;> simp [hs, hj]
  have hJ : Formalism.REAL.Jm ε = Matrix.diagonal (fun i => (s i : ℂ)) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext i
    cases hi : ε i <;> simp [hs, hi]
  rw [hJ] at h
  have hneg : Nᴴ * Matrix.diagonal (fun i => ((-s i : ℝ) : ℂ)) * N = Matrix.diagonal fun i => ((-x i : ℝ) : ℂ) := by
    have hd : ∀ v : Fin r → ℝ, Matrix.diagonal (fun i => ((-v i : ℝ) : ℂ)) = -Matrix.diagonal (fun i => (v i : ℂ)) := by
      intro v; ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hd, hd, Matrix.mul_neg, Matrix.neg_mul, h]
  have c1 := card_pos_le s x N h
  have c2 := card_pos_le (fun i => -s i) (fun i => -x i) N hneg
  have compl : ∀ v : Fin r → ℝ, (∀ i, v i ≠ 0) →
      Fintype.card {i // 0 < -v i} = r - Fintype.card {i // 0 < v i} := by
    intro v hv
    have hc := Fintype.card_subtype_compl (fun i => 0 < v i)
    simp only [Fintype.card_fin] at hc
    rw [← hc]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun h1 h2 => by linarith [neg_pos.1 h1], fun h1 => neg_pos.2 (lt_of_le_of_ne (not_lt.1 h1) (hv i))⟩)
  rw [compl s hs0, compl x hx] at c2
  have b1 := Fintype.card_subtype_le (fun i => 0 < s i)
  have b2 := Fintype.card_subtype_le (fun i => 0 < x i)
  simp only [Fintype.card_fin] at b1 b2
  have hAB : Fintype.card {i // 0 < x i} = Fintype.card {i // 0 < s i} := by omega
  have e1 : {i // 0 < x i} ≃ {j // 0 < s j} := Fintype.equivOfCardEq hAB
  have e2 : {i // ¬ 0 < x i} ≃ {j // ¬ 0 < s j} := by
    apply Fintype.equivOfCardEq
    clear c1 c2 compl b1 b2 hneg h hJ hs0 hsε hs e1
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    exact congrArg _ hAB
  clear c1 c2 compl b1 b2 hneg h hJ hs0 hs hAB
  refine ⟨Equiv.subtypeCongr e1 e2, funext fun i => ?_⟩
  show ε (Equiv.subtypeCongr e1 e2 i) = decide (0 < x i)
  by_cases h0 : 0 < x i
  · have hy : Equiv.subtypeCongr e1 e2 i = (e1 ⟨i, h0⟩ : Fin r) := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun j => 0 < x j) (a := i) h0]
      rfl
    rw [hy, decide_eq_true h0]
    simpa [hsε] using (e1 ⟨i, h0⟩).2
  · have hy : Equiv.subtypeCongr e1 e2 i = (e2 ⟨i, h0⟩ : Fin r) := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun j => 0 < x j) (a := i) h0]
      rfl
    rw [hy, decide_eq_false h0]
    simpa [hsε] using (e2 ⟨i, h0⟩).2

def permM (y : Equiv.Perm (Fin r)) : Matrix (Fin r) (Fin r) ℂ := fun i j => if i = y j then 1 else 0

theorem permM_mul_diagonal (y : Equiv.Perm (Fin r)) (c : Fin r → ℂ) :
    permM y * Matrix.diagonal c = Matrix.diagonal (fun i => c (y⁻¹ i)) * permM y := by
  ext i j
  simp only [permM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs with h
  · subst h
    simp
  · simp

theorem conjTranspose_permM_mul (y : Equiv.Perm (Fin r)) : (permM y)ᴴ * permM y = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (y i)]
  · simp [permM, Matrix.one_apply]
  · intro k _ hk
    simp [permM, hk]
  · simp

theorem permM_gram (ε : Fin r → Bool) (y : Equiv.Perm (Fin r)) :
    (permM y)ᴴ * Formalism.REAL.Jm ε * permM y = Formalism.REAL.Jm (ε ∘ y) := by
  have h1 : Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) * permM y =
      permM y * Matrix.diagonal (fun a => if ε (y a) then (1 : ℂ) else -1) := by
    rw [permM_mul_diagonal]
    simp
  simp only [Formalism.REAL.Jm, Function.comp_apply]
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, conjTranspose_permM_mul, Matrix.one_mul]

private lemma sign_lemma' (a : ℝ) (ha : a ≠ 0) :
    (Real.sqrt |a|)⁻¹ * a * (Real.sqrt |a|)⁻¹ = if 0 < a then 1 else -1 := by
  have hs : (Real.sqrt |a|)⁻¹ * (Real.sqrt |a|)⁻¹ = |a|⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg a)]
  calc (Real.sqrt |a|)⁻¹ * a * (Real.sqrt |a|)⁻¹ = a * ((Real.sqrt |a|)⁻¹ * (Real.sqrt |a|)⁻¹) := by ring
    _ = a * |a|⁻¹ := by rw [hs]
    _ = _ := by
      split_ifs with h
      · rw [abs_of_pos h, mul_inv_cancel₀ ha]
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) ha), inv_neg, mul_neg, mul_inv_cancel₀ ha]

theorem exists_conj_diag (ε : Fin r → Bool) (x : Fin r → ℝ) (hx : ∀ i, x i ≠ 0) (N : Matrix (Fin r) (Fin r) ℂ)
    (h : Nᴴ * Formalism.REAL.Jm ε * N = Matrix.diagonal fun i => (x i : ℂ)) (y : Equiv.Perm (Fin r))
    (hy : ε ∘ y = fun i => decide (0 < x i)) (m : Matrix (Fin r) (Fin r) ℂ) (c : Fin r → ℂ)
    (hm : m * N = N * Matrix.diagonal c) :
    ∃ G ∈ Formalism.MainNotions.S.UJset ε, G * m = Matrix.diagonal (fun i => c (y⁻¹ i)) * G := by
  classical
  have hPP : (permM y)ᴴ * permM y = 1 := conjTranspose_permM_mul y
  have hPP' : permM y * (permM y)ᴴ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (y⁻¹ i)]
    · by_cases hij : i = j
      · subst hij
        simp [permM]
      · simp [permM, Matrix.one_apply, hij, Ne.symm hij]
    · intro k _ hk
      have hik : i ≠ y k := fun e => hk (by simp [e])
      simp [permM, hik]
    · simp
  let S : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun i => (((Real.sqrt |x i|)⁻¹ : ℝ) : ℂ)
  have hS : Sᴴ = S := by simp [S, Matrix.diagonal_conjTranspose]
  have hSxS : S * Matrix.diagonal (fun i => (x i : ℂ)) * S = Formalism.REAL.Jm (ε ∘ y) := by
    rw [hy]
    simp only [S, Matrix.diagonal_mul_diagonal, Formalism.REAL.Jm]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, sign_lemma' (x i) (hx i)]
    by_cases h0 : 0 < x i <;> simp [h0]
  let Q : Matrix (Fin r) (Fin r) ℂ := N * S * (permM y)ᴴ
  have hQ : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε := by
    have e1 : Qᴴ * Formalism.REAL.Jm ε * Q = permM y * (S * (Nᴴ * Formalism.REAL.Jm ε * N) * S) * (permM y)ᴴ := by
      simp only [Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS, Matrix.mul_assoc]
    rw [e1, h, hSxS, ← permM_gram]
    calc permM y * ((permM y)ᴴ * Formalism.REAL.Jm ε * permM y) * (permM y)ᴴ
        = (permM y * (permM y)ᴴ) * Formalism.REAL.Jm ε * (permM y * (permM y)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPP', Matrix.one_mul, Matrix.mul_one]
  have hDc : Matrix.diagonal c * (permM y)ᴴ = (permM y)ᴴ * Matrix.diagonal (fun i => c (y⁻¹ i)) := by
    calc Matrix.diagonal c * (permM y)ᴴ = (permM y)ᴴ * (permM y * Matrix.diagonal c) * (permM y)ᴴ := by
          rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
      _ = (permM y)ᴴ * Matrix.diagonal (fun i => c (y⁻¹ i)) * (permM y * (permM y)ᴴ) := by
          rw [permM_mul_diagonal]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP', Matrix.mul_one]
  have hcS : Matrix.diagonal c * S = S * Matrix.diagonal c := by
    simp only [S, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hmQ : m * Q = Q * Matrix.diagonal (fun i => c (y⁻¹ i)) := by
    calc m * Q = (m * N) * S * (permM y)ᴴ := by simp only [Q, Matrix.mul_assoc]
      _ = N * (Matrix.diagonal c * S) * (permM y)ᴴ := by rw [hm]; simp only [Matrix.mul_assoc]
      _ = N * S * (Matrix.diagonal c * (permM y)ᴴ) := by rw [hcS]; simp only [Matrix.mul_assoc]
      _ = Q * Matrix.diagonal (fun i => c (y⁻¹ i)) := by rw [hDc]; simp only [Q, Matrix.mul_assoc]
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> norm_num
  have hdet : IsUnit Q.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm ε * Qᴴ * Formalism.REAL.Jm ε)
    calc Formalism.REAL.Jm ε * Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε * (Qᴴ * Formalism.REAL.Jm ε * Q) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ, hJJ]
  refine ⟨Q⁻¹, ?_, ?_⟩
  · show (Q⁻¹)ᴴ * Formalism.REAL.Jm ε * Q⁻¹ = Formalism.REAL.Jm ε
    calc (Q⁻¹)ᴴ * Formalism.REAL.Jm ε * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Q⁻¹ := by rw [hQ]
      _ = (Q * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by
          rw [Matrix.mul_nonsing_inv Q hdet, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · calc Q⁻¹ * m = Q⁻¹ * (m * Q) * Q⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hdet, Matrix.mul_one]
      _ = Matrix.diagonal (fun i => c (y⁻¹ i)) * Q⁻¹ := by
          rw [hmQ]
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul]

theorem exists_reps (ε : Fin r → Bool) (WK : Subgroup (Equiv.Perm (Fin r))) (hW : ∀ w, w ∈ WK ↔ ε ∘ w = ε)
    {X : Type} (sg : X → Fin r → Bool) (hi : Function.Injective sg)
    (h1 : ∀ q, ∃ y : Equiv.Perm (Fin r), ε ∘ y = sg q) (h2 : ∀ y : Equiv.Perm (Fin r), ∃ q, sg q = ε ∘ y) :
    ∃ (T : Finset (Equiv.Perm (Fin r))) (b : X ≃ T),
      Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin r)))⁻¹ * (p.1 : Equiv.Perm (Fin r))) ∧
      ∀ q, ε ∘ (b q : Equiv.Perm (Fin r)) = sg q := by
  classical
  choose yq hyq using h1
  have hinj : Function.Injective yq := fun q q' e => hi (by rw [← hyq q, ← hyq q', e])
  let T : Finset (Equiv.Perm (Fin r)) := Finset.univ.filter (fun t => t ∈ Set.range yq)
  have memT : ∀ t, t ∈ T ↔ ∃ q, yq q = t := by
    intro t
    simp [T]
  let b : X ≃ T := Equiv.ofBijective (fun q => ⟨yq q, (memT _).2 ⟨q, rfl⟩⟩)
    ⟨fun q q' e => hinj (congrArg Subtype.val e), fun t => by
      obtain ⟨q, hq⟩ := (memT t.1).1 t.2
      exact ⟨q, Subtype.ext hq⟩⟩
  have key : ∀ w ∈ WK, ∀ t : Equiv.Perm (Fin r), ε ∘ ⇑(w⁻¹ * t) = ε ∘ ⇑t := by
    intro w hw t
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, (hW _).1 (WK.inv_mem hw)]
  refine ⟨T, b, ⟨?_, ?_⟩, fun q => hyq q⟩
  · rintro ⟨w, t⟩ ⟨w', t'⟩ he
    simp only at he
    have he' := congrArg (fun z : Equiv.Perm (Fin r) => z⁻¹) he
    simp only [mul_inv_rev, inv_inv] at he'
    have e1 : ε ∘ ⇑(t : Equiv.Perm (Fin r)) = ε ∘ ⇑(t' : Equiv.Perm (Fin r)) := by
      rw [← key w w.2 t, he', key w' w'.2 t']
    obtain ⟨q, hq⟩ := (memT _).1 t.2
    obtain ⟨q', hq'⟩ := (memT _).1 t'.2
    have hqq : q = q' := hi (by rw [← hyq q, ← hyq q', hq, hq', e1])
    have htt : t = t' := Subtype.ext (by rw [← hq, ← hq', hqq])
    subst htt
    have hww : w = w' := Subtype.ext (mul_left_cancel he)
    rw [hww]
  · intro s
    obtain ⟨q, hq⟩ := h2 s⁻¹
    have htT : yq q ∈ T := (memT _).2 ⟨q, rfl⟩
    have hw : yq q * s ∈ WK := by
      rw [hW, Equiv.Perm.coe_mul, ← Function.comp_assoc, hyq q, hq, Function.comp_assoc,
        ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one, Function.comp_id]
    exact ⟨(⟨yq q * s, hw⟩, ⟨yq q, htT⟩), by simp⟩

end Mat

section Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  {P : PPol σ r} {w : InfinitePlace F} {τ : EmbOver E w} {J : Matrix (Fin r) (Fin r) E}
  {Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ)}

theorem infEmb_hform (hc : IsCMExt F E σ) (u v : Fin r → w.Completion ⊗[F] E) :
    infEmb τ (Formalism.UG.hform (sigR w.Completion σ) (JR w.Completion J) u v) =
      star (infEmb τ ∘ u) ⬝ᵥ (J.map τ.1 *ᵥ (infEmb τ ∘ v)) := by
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, dotProduct, Matrix.mulVec, Function.comp_apply, Pi.star_apply, Finset.mul_sum,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hJ : infEmb τ (JR w.Completion J i j) = τ.1 (J i j) := by
    rw [JR, Matrix.map_apply, inclR]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, infEmb_tmul,
      map_one, one_mul]
  rw [← infEmb_sigR hc τ, hJ, starRingEnd_apply]
  ring

theorem infEmb_hx (h1 : ∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i))
    (h4 : ∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) (x y y' : w.Completion ⊗[F] Fld P) :
    infEmb τ (hx P w.Completion x y y') = star (Ψ y') ⬝ᵥ (Matrix.diagonal (Ψ x) *ᵥ Ψ y) := by
  rw [hx, h4]
  simp only [map_mul, Pi.mul_apply, h1, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem Psi_units_ne_zero (u : (w.Completion ⊗[F] Fld P)ˣ) (i : Fin r) :
    Ψ (u : w.Completion ⊗[F] Fld P) i ≠ 0 := by
  intro h0
  have h2 := congrArg (fun z => Ψ z i) u.mul_inv
  simp only [map_mul, Pi.mul_apply, h0, zero_mul, map_one, Pi.one_apply] at h2
  exact zero_ne_one h2

theorem plus_real (h1 : ∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) (x : plusUnits P w.Completion)
    (i : Fin r) : ((Ψ x.1.1 i).re : ℂ) = Ψ x.1.1 i ∧ (Ψ x.1.1 i).re ≠ 0 := by
  have hfix : sigR w.Completion (star' P) x.1.1 = x.1.1 := by
    have h0 := congrArg Units.val
      (show Units.map (sigR w.Completion (star' P)).toMonoidHom x.1 = x.1 from x.2)
    simpa using h0
  have hr : conj (Ψ x.1.1 i) = Ψ x.1.1 i := by rw [← h1, hfix]
  have hre : ((Ψ x.1.1 i).re : ℂ) = Ψ x.1.1 i := Complex.conj_eq_iff_re.1 hr
  refine ⟨hre, fun h0 => Psi_units_ne_zero (Ψ := Ψ) x.1 i ?_⟩
  rw [← hre, h0, Complex.ofReal_zero]

private theorem Psi_inv_units_eq_inv (u : (w.Completion ⊗[F] Fld P)ˣ) (i : Fin r) :
    Ψ ((u⁻¹ : (w.Completion ⊗[F] Fld P)ˣ) : w.Completion ⊗[F] Fld P) i = (Ψ (u : w.Completion ⊗[F] Fld P) i)⁻¹ := by
  have h2 := congrArg (fun z => Ψ z i) u.mul_inv
  simp only [map_mul, Pi.mul_apply, map_one, Pi.one_apply] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem mk_eq_iff_sign (h1 : ∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i))
    (x x' : plusUnits P w.Completion) : (QuotientGroup.mk x : Cls P w.Completion) = QuotientGroup.mk x' ↔
      ∀ i, 0 < (Ψ x.1.1 i).re ↔ 0 < (Ψ x'.1.1 i).re := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, norms, MonoidHom.mem_range]
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · rintro ⟨c, hc⟩ i
    have hv : (c : w.Completion ⊗[F] Fld P) * sigR w.Completion (star' P) c =
        ((x.1⁻¹ : (w.Completion ⊗[F] Fld P)ˣ) : w.Completion ⊗[F] Fld P) * x'.1.1 := by
      have h0 := congrArg Units.val hc
      simpa using h0
    have hv2 := congrArg (fun z => Ψ z i) hv
    simp only [map_mul, Pi.mul_apply, h1, Psi_inv_units_eq_inv] at hv2
    obtain ⟨hxr, hx0⟩ := plus_real h1 x i
    obtain ⟨hyr, -⟩ := plus_real h1 x' i
    rw [Complex.mul_conj, ← hxr, ← hyr] at hv2
    have hn : Complex.normSq (Ψ (c : w.Completion ⊗[F] Fld P) i) = (Ψ x.1.1 i).re⁻¹ * (Ψ x'.1.1 i).re := by
      exact_mod_cast hv2
    have hpos : 0 < (Ψ x.1.1 i).re⁻¹ * (Ψ x'.1.1 i).re := by
      rw [← hn]
      exact Complex.normSq_pos.2 (Psi_units_ne_zero (Ψ := Ψ) c i)
    rcases mul_pos_iff.mp hpos with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨fun _ => hb, fun _ => inv_pos.mp ha⟩
    · constructor
      · intro h
        exact absurd (inv_pos.mpr h) (not_lt.mpr ha.le)
      · intro h
        exact absurd h (not_lt.mpr hb.le)
  · intro hs
    have hq : ∀ i, 0 < (Ψ x.1.1 i).re⁻¹ * (Ψ x'.1.1 i).re := by
      intro i
      have ha := (plus_real h1 x i).2
      have hb := (plus_real h1 x' i).2
      rcases lt_or_gt_of_ne ha with ha' | ha'
      · have hb' : (Ψ x'.1.1 i).re < 0 := by
          rcases lt_or_gt_of_ne hb with hb' | hb'
          · exact hb'
          · exact absurd ((hs i).2 hb') (not_lt.mpr ha'.le)
        exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr ha') hb'
      · exact mul_pos (inv_pos.mpr ha') ((hs i).1 ha')
    set v : Fin r → ℂ := fun i => ((Real.sqrt ((Ψ x.1.1 i).re⁻¹ * (Ψ x'.1.1 i).re) : ℝ) : ℂ) with hvdef
    have hv0 : ∀ i, v i ≠ 0 := by
      intro i
      simp only [hvdef, ne_eq, Complex.ofReal_eq_zero]
      exact (Real.sqrt_pos.2 (hq i)).ne'
    refine ⟨Units.map (Ψ.symm : (Fin r → ℂ) →* w.Completion ⊗[F] Fld P) ⟨v, fun i => (v i)⁻¹, ?_, ?_⟩, Units.ext ?_⟩
    · funext i
      simp [hv0 i]
    · funext i
      simp [hv0 i]
    apply Ψ.injective
    funext i
    obtain ⟨hxr, -⟩ := plus_real h1 x i
    obtain ⟨hyr, -⟩ := plus_real h1 x' i
    change Ψ (Ψ.symm v * sigR w.Completion (star' P) (Ψ.symm v)) i =
      Ψ (((x.1⁻¹ : (w.Completion ⊗[F] Fld P)ˣ) : w.Completion ⊗[F] Fld P) * x'.1.1) i
    rw [map_mul, Pi.mul_apply, map_mul, Pi.mul_apply, h1, RingEquiv.apply_symm_apply, Psi_inv_units_eq_inv, ← hxr,
      ← hyr]
    simp only [hvdef]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hq i).le, Complex.ofReal_mul,
      Complex.ofReal_inv]

private theorem torUnit_diagH_alphaRat_eq_one_tmul_alpha {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
    (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k] :
    ((torUnit (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH (star' P) (one₁ P) k (alphaRat P)) : (k ⊗[F] Fld P)ˣ) : k ⊗[F] Fld P) =
      1 ⊗ₜ[F] alpha P := by
  change Matrix.det ((HA.mat k (star' P) (one₁ P) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH (star' P) (one₁ P) k (alphaRat P)) :
    GL (Fin 1) (k ⊗[F] Fld P)) : Matrix (Fin 1) (Fin 1) (k ⊗[F] Fld P)) = _
  rw [Matrix.det_unique]
  show ((Matrix.scalar (Fin 1) (alpha P)).map (fun a => (1 : k) ⊗ₜ[F] a)) 0 0 = 1 ⊗ₜ[F] alpha P
  simp

theorem exists_matrix (hc : IsCMExt F E σ) (h1 : ∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i))
    (h2 : ∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e)
    (h4 : ∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) {x : w.Completion ⊗[F] Fld P}
    {φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)}
    (h : IsIsom P w.Completion J x φ) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, Nᴴ * J.map τ.1 * N = Matrix.diagonal (Ψ x) ∧
      archMat σ J τ (gam h) * N = N * Matrix.diagonal (Ψ (1 ⊗ₜ[F] alpha P)) := by
  classical
  have hsurj := (infEmb_bijective hc τ).2
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin r) (Fin r) ℂ, ∀ y, infEmb τ ∘ φ y = N *ᵥ Ψ y := by
    refine ⟨Matrix.of fun i j => infEmb τ (φ (Ψ.symm (Pi.single j 1)) i), fun y => ?_⟩
    choose e he using fun j => hsurj (Ψ y j)
    have hy : y = ∑ j, e j • Ψ.symm (Pi.single j 1) := by
      apply Ψ.injective
      funext i
      rw [map_sum, Finset.sum_apply]
      simp only [Algebra.smul_def, map_mul, Pi.mul_apply, h2, he, RingEquiv.apply_symm_apply, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    funext i
    conv_lhs => rw [hy]
    simp only [Function.comp_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul, he,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨N, ?_, ?_⟩
  · have key : ∀ a b : Fin r → ℂ, a ⬝ᵥ ((Nᴴ * J.map τ.1 * N) *ᵥ b) = a ⬝ᵥ (Matrix.diagonal (Ψ x) *ᵥ b) := by
      intro a b
      have e1 := infEmb_hform (J := J) (τ := τ) hc (φ (Ψ.symm (star a))) (φ (Ψ.symm b))
      rw [h, infEmb_hx h1 h4, hN, hN, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, star_star,
        Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, star_star] at e1
      exact e1.symm
    ext i j
    have e2 : (Nᴴ * J.map τ.1 * N) i j = (Pi.single i (1 : ℂ) : Fin r → ℂ) j * Ψ x j := by simpa using key (Pi.single i 1) (Pi.single j 1)
    rw [e2, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  · have ht := torUnit_diagH_alphaRat_eq_one_tmul_alpha P w.Completion
    have hg : ((matHom w.Completion σ J (gam h) : GL (Fin r) (w.Completion ⊗[F] E)) :
        Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E)) = mulMat φ (1 ⊗ₜ[F] alpha P) := by
      rw [← ht]; rfl
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := Ψ.surjective v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hN, archMat_apply]
    have hm : ((matHom w.Completion σ J (gam h)).1.map (infEmb τ)) *ᵥ (infEmb τ ∘ φ y) =
        infEmb τ ∘ (mulMat φ (1 ⊗ₜ[F] alpha P) *ᵥ φ y) := by
      rw [← hg]
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [hm, mulMat_mulVec, hN, map_mul]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl

theorem exists_isIsom (hc : IsCMExt F E σ) (h1 : ∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i))
    (h2 : ∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e)
    (h4 : ∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) (x : w.Completion ⊗[F] Fld P)
    (N : Matrix (Fin r) (Fin r) ℂ) (hN : IsUnit N.det) (h : Nᴴ * J.map τ.1 * N = Matrix.diagonal (Ψ x)) :
    ∃ φ, IsIsom P w.Completion J x φ := by
  classical
  have hbij := infEmb_bijective hc τ
  obtain ⟨ι, hι'⟩ : ∃ ι : w.Completion ⊗[F] E ≃+* ℂ, ∀ a, infEmb τ a = ι a :=
    ⟨RingEquiv.ofBijective (infEmb τ) hbij, fun _ => rfl⟩
  have hsm : ∀ (e : w.Completion ⊗[F] E) (y : w.Completion ⊗[F] Fld P), Ψ (e • y) = ι e • Ψ y := by
    intro e y
    rw [Algebra.smul_def, map_mul]
    funext i
    simp [h2, hι']
  obtain ⟨f, hf⟩ : ∃ f : (w.Completion ⊗[F] Fld P) →ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E),
      ∀ y i, ι (f y i) = (N *ᵥ Ψ y) i := by
    refine ⟨{ toFun := fun y i => ι.symm ((N *ᵥ Ψ y) i)
              map_add' := fun y y' => ?_
              map_smul' := fun e y => ?_ }, fun y i => by simp⟩
    · funext i
      apply ι.injective
      simp [Matrix.mulVec_add]
    · funext i
      apply ι.injective
      simp [hsm, Matrix.mulVec_smul]
  have hinj : Function.Injective f := by
    intro y y' hyy
    have e1 : N *ᵥ Ψ y = N *ᵥ Ψ y' := funext fun i => by rw [← hf, ← hf, hyy]
    have e2 := congrArg (fun v => N⁻¹ *ᵥ v) e1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hN, Matrix.one_mulVec] at e2
    exact Ψ.injective e2
  have hsur : Function.Surjective f := by
    intro u
    refine ⟨Ψ.symm (N⁻¹ *ᵥ fun i => ι (u i)), ?_⟩
    funext i
    apply ι.injective
    rw [hf, RingEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsur⟩, ?_⟩
  intro y y'
  have hφ : ∀ z, infEmb τ ∘ (LinearEquiv.ofBijective f ⟨hinj, hsur⟩) z = N *ᵥ Ψ z := fun z => by
    funext i
    rw [Function.comp_apply, hι']
    exact hf z i
  apply ι.injective
  rw [← hι', ← hι', infEmb_hform (J := J) (τ := τ) hc, infEmb_hx h1 h4, hφ, hφ, ← h, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Bridge

theorem real_classes : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i) := by
  intro D V S M P ρ hT WK hW
  classical
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  obtain ⟨Ψ, h1, h2, hα, h4, -, -⟩ :=
    GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow D.host.F D.host.E D.sp.cm.sig hc V.rank P (placeOf D ρ) (embOverOf D ρ) hT
  have hfr := M.fr_gram ρ
  have hgram : gramAt D V ρ = V.gram.map (embOverOf D ρ).1 := rfl
  have hFu : IsUnit (M.fr ρ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  obtain ⟨sg, hsg⟩ : ∃ sg : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → Bool,
      ∀ q i, sg q i = decide (0 < (Ψ (Quotient.out q.1).1.1 i).re) := ⟨fun q i => _, fun _ _ => rfl⟩
  have hsign : ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (x : plusUnits P (placeOf D ρ).Completion),
      (QuotientGroup.mk x : Cls P (placeOf D ρ).Completion) = q.1 → sg q = fun i => decide (0 < (Ψ x.1.1 i).re) := by
    intro q x hx
    funext i
    rw [hsg]
    exact decide_eq_decide.2 ((mk_eq_iff_sign h1 _ _).1 ((Quotient.out_eq q.1).trans hx.symm) i)

  have hframe : ∀ (x : plusUnits P (placeOf D ρ).Completion) (N : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      Nᴴ * V.gram.map (embOverOf D ρ).1 * N = Matrix.diagonal (Ψ x.1.1) →
      (M.fr ρ * N)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * N) = Matrix.diagonal fun i => ((Ψ x.1.1 i).re : ℂ) := by
    intro x N hN
    have hd : Matrix.diagonal (Ψ x.1.1) = Matrix.diagonal fun i => ((Ψ x.1.1 i).re : ℂ) := by
      congr 1
      funext i
      exact ((plus_real h1 x i).1).symm
    rw [← hd, ← hN, ← hgram, ← hfr, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ q : XSet P (placeOf D ρ).Completion V.gram, ∃ y : Equiv.Perm (Fin V.rank), M.ε ρ ∘ y = sg q := by
    intro q
    obtain ⟨x, φ, hxq, hiso⟩ := q.2
    obtain ⟨N, hN1, -⟩ := exists_matrix hc h1 h2 h4 hiso
    obtain ⟨y, hy⟩ := exists_perm (M.ε ρ) (fun i => (Ψ x.1.1 i).re) (fun i => (plus_real h1 x i).2) _
      (hframe x N hN1)
    exact ⟨y, hy.trans (hsign q x hxq).symm⟩
  have hPu : ∀ y : Equiv.Perm (Fin V.rank), IsUnit (permM y).det := by
    intro y
    have e := congrArg Matrix.det (conjTranspose_permM_mul y)
    rw [Matrix.det_mul, Matrix.det_one] at e
    exact ⟨⟨_, _, (mul_comm _ _).trans e, e⟩, rfl⟩
  have hB : ∀ y : Equiv.Perm (Fin V.rank), ∃ q, sg q = M.ε ρ ∘ y := by
    intro y
    have hu : IsUnit (fun i => if M.ε ρ (y i) then (1 : ℂ) else -1) :=
      Pi.isUnit_iff.2 fun i => by by_cases h : M.ε ρ (y i) <;> simp [h, isUnit_iff_ne_zero]
    have hu' : IsUnit (Ψ.symm fun i => if M.ε ρ (y i) then (1 : ℂ) else -1) :=
      (isUnit_map_iff Ψ _).1 (by rw [RingEquiv.apply_symm_apply]; exact hu)
    obtain ⟨xP, hxP⟩ : ∃ xP : plusUnits P (placeOf D ρ).Completion,
        Ψ xP.1.1 = fun i => if M.ε ρ (y i) then (1 : ℂ) else -1 := by
      refine ⟨⟨hu'.unit, ?_⟩, by simp⟩
      ext1
      show sigR (placeOf D ρ).Completion (star' P) (Ψ.symm fun i => if M.ε ρ (y i) then (1 : ℂ) else -1) =
        Ψ.symm fun i => if M.ε ρ (y i) then (1 : ℂ) else -1
      apply Ψ.injective
      funext i
      rw [h1, RingEquiv.apply_symm_apply]
      by_cases h : M.ε ρ (y i) <;> simp [h]
    have hi : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFu
    have hi' : ((M.fr ρ)⁻¹)ᴴ * (M.fr ρ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
    have e : ((M.fr ρ)⁻¹ * permM y)ᴴ * V.gram.map (embOverOf D ρ).1 * ((M.fr ρ)⁻¹ * permM y) =
        Matrix.diagonal (Ψ xP.1.1) := by
      rw [hxP, ← hgram, ← hfr, Matrix.conjTranspose_mul]
      calc (permM y)ᴴ * ((M.fr ρ)⁻¹)ᴴ * ((M.fr ρ)ᴴ * Formalism.REAL.Jm (M.ε ρ) * M.fr ρ) * ((M.fr ρ)⁻¹ * permM y)
          = (permM y)ᴴ * (((M.fr ρ)⁻¹)ᴴ * (M.fr ρ)ᴴ) * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) * permM y := by
            simp only [Matrix.mul_assoc]
        _ = (permM y)ᴴ * Formalism.REAL.Jm (M.ε ρ) * permM y := by rw [hi, hi', Matrix.mul_one, Matrix.mul_one]
        _ = Formalism.REAL.Jm (M.ε ρ ∘ y) := permM_gram _ _
        _ = _ := rfl
    have hNu : IsUnit ((M.fr ρ)⁻¹ * permM y).det := by
      rw [Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det _ hFu).mul (hPu y)
    obtain ⟨φ0, hφ0⟩ := exists_isIsom hc h1 h2 h4 xP.1.1 _ hNu e
    refine ⟨⟨QuotientGroup.mk xP, xP, φ0, rfl, hφ0⟩, ?_⟩
    rw [hsign _ xP rfl, hxP]
    funext i
    by_cases h : M.ε ρ (y i) <;> simp [h]
  have hinj : Function.Injective sg := by
    intro q q' hq
    apply Subtype.ext
    have e := (mk_eq_iff_sign h1 (Quotient.out q.1) (Quotient.out q'.1)).2 fun i =>
      decide_eq_decide.1 (by rw [← hsg, ← hsg, hq])
    exact (Quotient.out_eq q.1).symm.trans (e.trans (Quotient.out_eq q'.1))
  have hW' : ∀ w, w ∈ WK ↔ M.ε ρ ∘ w = M.ε ρ := fun w => (hW w).trans (by simp [GlobalTheory.HCChar.compactWeyl])
  obtain ⟨T, b, hbij, hb⟩ := exists_reps (M.ε ρ) WK hW' sg hinj hA hB
  refine ⟨T, b, hbij, ?_⟩
  intro q γ hγ
  obtain ⟨x, φ, hiso, hxq, rfl⟩ := hγ
  obtain ⟨N, hN1, hN2⟩ := exists_matrix hc h1 h2 h4 hiso
  have hy : M.ε ρ ∘ (b q : Equiv.Perm (Fin V.rank)) = fun i => decide (0 < (Ψ x.1.1 i).re) :=
    (hb q).trans (hsign q x hxq)
  have hm : frameMat M ρ (gam hiso) * (M.fr ρ * N) =
      (M.fr ρ * N) * Matrix.diagonal (cxRoots (embOverOf D ρ).1 P) := by
    have hfm : frameMat M ρ (gam hiso) =
        M.fr ρ * archMat D.sp.cm.sig V.gram (embOverOf D ρ) (gam hiso) * (M.fr ρ)⁻¹ := rfl
    rw [hfm, ← hα]
    calc M.fr ρ * archMat D.sp.cm.sig V.gram (embOverOf D ρ) (gam hiso) * (M.fr ρ)⁻¹ * (M.fr ρ * N)
        = M.fr ρ * archMat D.sp.cm.sig V.gram (embOverOf D ρ) (gam hiso) * ((M.fr ρ)⁻¹ * M.fr ρ) * N := by
          simp only [Matrix.mul_assoc]
      _ = M.fr ρ * (archMat D.sp.cm.sig V.gram (embOverOf D ρ) (gam hiso) * N) := by
          rw [Matrix.nonsing_inv_mul _ hFu, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hN2, Matrix.mul_assoc]
  obtain ⟨G, hG, hGm⟩ := exists_conj_diag (M.ε ρ) (fun i => (Ψ x.1.1 i).re) (fun i => (plus_real h1 x i).2) _
    (hframe x N hN1) (b q) hy _ _ hm
  obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ hG
  refine ⟨g, ?_⟩
  have hinv : G * frameMat M ρ g⁻¹ = 1 := by
    rw [← hg, ← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, hg, hGm, Matrix.mul_assoc, hinv, Matrix.mul_one]

end GlobalTheory.TrEll.RealClasses
