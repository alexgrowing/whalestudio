import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.BlockSubst

def firstCols (D₁ D₂ : Type) [Fintype D₁] [Fintype D₂] : D₁ ≃ ↥(Assignment.one.block D₁ D₂) where
  toFun j := ⟨Sum.inl j, by simp [Assignment.block]⟩
  invFun x := Sum.getLeft x.1 (by simpa [Assignment.block] using x.2)
  left_inv j := rfl
  right_inv x := by
    obtain ⟨x | x, hx⟩ := x
    · rfl
    · simp [Assignment.block] at hx

theorem forall_mem_block_one {D₁ D₂ : Type} [Fintype D₁] [Fintype D₂] (p : D₁ ⊕ D₂ → Prop) :
    (∀ j ∈ Assignment.one.block D₁ D₂, p j) ↔ ∀ j : D₁, p (Sum.inl j) := by
  constructor
  · intro h j; exact h _ (by simp [Assignment.block])
  · rintro h (j | j) hj
    · exact h j
    · simp [Assignment.block] at hj

theorem sum_mul_eq_trace {A D : Type} [Fintype A] [Fintype D] {k : Type} [Field k] (X Z : Matrix A D k) :
    ∑ i, ∑ j, X i j * Z i j = trace (X * Zᵀ) := by
  simp [trace, Matrix.mul_apply]

end GlobalTheory.BlockSubst

open GlobalTheory.BlockSubst in
theorem GlobalTheory.BlockSubst.fourierSum_blockDiag_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ Y : Matrix A (D₁ ⊕ D₂) k,
      fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) Y =
        fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂ Y
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  set P := Assignment.one.block D₁ D₂ with hP
  set E := firstCols D₁ D₂ with hE
  set c : k := ((ϖ ^ e : kˣ) : k) with hc
  obtain ⟨hM1, hM1'⟩ := (mem_KO_iff M₁).1 hM₁
  obtain ⟨hT1, hT1'⟩ := (mem_KO_iff _).1 (invT_mem_KO hM₁)
  have hsumP : ∀ f : ↥P → k, ∑ j : ↥P, f j = ∑ j : D₁, f (E j) := fun f =>
    (Fintype.sum_equiv E _ _ fun _ => rfl).symm
  have hX1 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inl j) = ∑ l, X i (Sum.inl l) * a l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  have hX2 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inr j) = ∑ l, X i (Sum.inr l) * b l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  set Y₁ : Matrix A D₁ k := Matrix.of fun i j => Y i (Sum.inl j) with hY₁
  have hYH : ∀ i j, (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i (Sum.inl j) = (Y₁ * (invT M₁).val) i j := by
    intro i j; rw [hX1]; simp [Y₁, Matrix.mul_apply]
  have hinv : (invT M₁).val * M₁.valᵀ = 1 := by
    rw [invT_val, ← transpose_mul, Units.mul_inv, transpose_one]
  have hinv' : M₁.val * ((invT M₁).val)ᵀ = 1 := by
    rw [invT_val, transpose_transpose, Units.mul_inv]
  have hint : ∀ (X : Matrix A D₁ k) (B : Matrix D₁ D₁ k), (∀ i j, B i j ∈ 𝒪[k]) →
      (∀ i j, c * X i j ∈ 𝒪[k]) → ∀ i j, c * (X * B) i j ∈ 𝒪[k] := by
    intro X B hB hX i j
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Subring.sum_mem _ fun l _ => by rw [← mul_assoc]; exact mul_mem (hX i l) (hB l j)
  have hcond : (∀ i, ∀ j ∈ P, c * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ P, c * (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i j ∈ 𝒪[k]) := by
    simp only [hP, forall_mem_block_one, hYH]
    constructor
    · intro h; exact hint Y₁ _ hT1 h
    · intro h i j
      have := hint _ M₁.valᵀ (fun i j => by simpa using hM1 j i) h i j
      rwa [Matrix.mul_assoc, hinv, Matrix.mul_one] at this
  set YH := Y * fromBlocks (invT M₁).val 0 0 M₂.val with hYHdef
  have hset : ∀ T' : Matrix A ↥P k, setCols P YH (T' * M₁.val.submatrix E.symm E.symm) =
      setCols P Y T' * fromBlocks M₁.val 0 0 M₂.val := by
    intro T'
    ext i (j | j)
    · rw [hX1]
      simp only [setCols, Matrix.of_apply]
      rw [dif_pos (by simp [hP, Assignment.block]), Matrix.mul_apply, hsumP]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dif_pos (by simp [hP, Assignment.block])]
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      rfl
    · rw [hX2]
      simp only [setCols, Matrix.of_apply]
      rw [dif_neg (by simp [hP, Assignment.block]), hYHdef, hX2]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dif_neg (by simp [hP, Assignment.block])]
  have hpc : ∀ (Z : Matrix A (D₁ ⊕ D₂) k) (S : Matrix A ↥P k),
      pairCols P Z S = ∑ i, ∑ j : D₁, S i (E j) * Z i (Sum.inl j) := by
    intro Z S; simp only [pairCols]; exact Finset.sum_congr rfl fun i _ => hsumP _
  have hpair : ∀ T' : Matrix A ↥P k, pairCols P YH (T' * M₁.val.submatrix E.symm E.symm) = pairCols P Y T' := by
    intro T'
    set T₁ : Matrix A D₁ k := Matrix.of fun i j => T' i (E j) with hT₁
    have hTN : ∀ i j, (T' * M₁.val.submatrix E.symm E.symm) i (E j) = (T₁ * M₁.val) i j := by
      intro i j; rw [Matrix.mul_apply, hsumP]; simp [T₁, Matrix.mul_apply]
    rw [hpc, hpc]
    simp only [hTN, hYH]
    calc ∑ i, ∑ j, (T₁ * M₁.val) i j * (Y₁ * (invT M₁).val) i j
        = trace ((T₁ * M₁.val) * (Y₁ * (invT M₁).val)ᵀ) := sum_mul_eq_trace _ _
      _ = trace (T₁ * Y₁ᵀ) := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M₁.val, hinv', Matrix.one_mul]
      _ = ∑ i, ∑ j, T' i (E j) * Y i (Sum.inl j) := (sum_mul_eq_trace T₁ Y₁).symm
  rw [fourierSum_apply, fourierSum_apply]
  beta_reduce
  split_ifs with h1 h2 h2
  · congr 1
    obtain ⟨u, hu⟩ := hM₁
    let N : Matrix ↥P ↥P 𝒪[k] := u.val.submatrix E.symm E.symm
    let N' : Matrix ↥P ↥P 𝒪[k] := (u⁻¹).val.submatrix E.symm E.symm
    have hN : N * N' = 1 := by
      simp only [N, N', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
    have hNk : N.map (fun x => (x : k)) = M₁.val.submatrix E.symm E.symm := by
      rw [← hu]; rfl
    have hF : ∀ T Z : Matrix A ↥P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        Φ (setCols P YH (T + Z)) * (ψ (pairCols P YH (T + Z)) : ℂ) =
          Φ (setCols P YH T) * (ψ (pairCols P YH T) : ℂ) := by
      intro T Z hZ
      have e1 : setCols P YH (T + Z) = setCols P YH T + setCols P 0 Z := by
        ext i j; by_cases hj : j ∈ P <;> simp [setCols, hj]
      have e2 : pairCols P YH (T + Z) = pairCols P YH T + pairCols P YH Z := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      rw [e1, e2, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P YH Z), mul_one]
      · refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        have h3 := (Valuation.mem_integer_iff _ _).1 (h2 i j j.2)
        rw [map_mul] at h3
        rw [Valuation.mem_integer_iff, map_mul]
        exact (show valuation k (Z i j) * valuation k (YH i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) * valuation k (YH i j) by
          gcongr; exact hZ i j).trans h3
      · refine FourierDepth.mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simpa [setCols, hj] using hZ i ⟨j, hj⟩
        · simp [setCols, hj]
    have key : ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T * N.map (fun x => (x : k)))) *
          (ψ (pairCols P YH (liftRes T * N.map (fun x => (x : k)))) : ℂ) =
        ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T)) * (ψ (pairCols P YH (liftRes T)) : ℂ) :=
      GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hN (fun T' => Φ (setCols P YH T') * (ψ (pairCols P YH T') : ℂ)) hF
    rw [← key, hNk]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hset, hpair]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl
