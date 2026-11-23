import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealKVCompatU
import Formalism.LocalToGlobal.IndefiniteReal.FockModel2
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
  Formalism.IndefR.WeilFull Formalism.IndefR.Fock.Exist Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.IoExist

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Blocks

variable {m : ℕ}

def blk1 (p : D.what₂.Tau → ℕ) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : complexSquareMatrixFamily D p :=
  fun τ => Matrix.of fun i j => if h : (i : ℕ) < m ∧ (j : ℕ) < m then k τ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def blk2 (p : D.what₂.Tau → ℕ) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : complementBlockMatrixFamily D m p :=
  fun τ => Matrix.of fun i j =>
    k τ ⟨p τ + (i : ℕ), by have := i.isLt; omega⟩ ⟨p τ + (j : ℕ), by have := j.isLt; omega⟩

open Classical in

def kAt (τ : D.what₂.Tau) (k : Matrix (Fin m) (Fin m) ℂ) : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ :=
  Function.update (fun _ => 1) τ k

end Blocks

def hOf (θ : InfFam D) (V : HSp D) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (u : GA D V) :
    HFam D V.rank :=
  fun τ => (BV τ)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) u * BV τ

open Classical in

def IoPi (θ : InfFam D) (V W : HSp D) {S' : D.what₂.Tau → SPar} (M : DSModel W S') (c : CoefA V)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (Δ : PolF D W.rank V.rank) : Prop :=
  ∃ io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank,
    (∀ u ∈ GinfC V, ∀ x w, io x (c.ρ u w) =
      piAct p a e (fun _ => 1) (fun _ => 1) (hOf θ V BV u) (io x w)) ∧
    (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ w,
        io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w =
          piAct p a e (blk1 p (kAt τ k)) (blk2 p (kAt τ k)) (fun _ => 1) (io (PiTensorProduct.tprod ℂ v) w)) ∧
    ∃ (v : ∀ ρ, lowT M ρ) (w : c.W), (∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧
      io (PiTensorProduct.tprod ℂ v) w = Δ

def KVWeightAt (N p n : ℕ) (κ : ℚ) (ap am : ℕ → ℕ) (Λ : Fin N → ℝ) : Prop :=
  p ≤ N ∧ Antitone ap ∧ Antitone am ∧ (∀ i, p ≤ i → ap i = 0) ∧ (∀ b, N - p ≤ b → am b = 0) ∧
    ((Finset.range p).filter (fun i => ap i ≠ 0)).card + ((Finset.range (N - p)).filter (fun b => am b ≠ 0)).card ≤ n ∧
    ∀ a : Fin N, Λ a =
      if (a : ℕ) < p then (ap a : ℝ) + (n : ℝ) / 2 + (κ : ℝ)
      else -(am (N - 1 - a) : ℝ) - (n : ℝ) / 2 + (κ : ℝ)

def nuDelta (n m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau)
    (c : Fin n) : ℤ :=
  -(ap τ c : ℤ) + (am τ (n - 1 - c) : ℤ) - dExp m p e τ

def IsCWt (θ : InfFam D) (V : HSp D) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : CoefA V)
    (μ : D.what₂.Tau → Fin V.rank → ℤ) (w : c.W) : Prop :=
  ∀ u ∈ GinfC V, ∀ t : D.what₂.Tau → Fin V.rank → ℂ, (∀ τ i, ‖t τ i‖ = 1) →
    (∀ τ, hOf θ V BV u τ = Matrix.diagonal (t τ)) → c.ρ u w = (∏ τ, ∏ i, t τ i ^ μ τ i) • w

def CoefLowWt (θ : InfFam D) (V : HSp D) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : CoefA V)
    (ν : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  (∃ w, w ≠ 0 ∧ IsCWt θ V BV c ν w) ∧
    ∀ μ w, w ≠ 0 → IsCWt θ V BV c μ w → ∀ τ, ∃ r : Fin V.rank → Fin V.rank → ℕ, (∀ a b, r a b ≠ 0 → a < b) ∧
      ∀ i, μ τ i - ν τ i = ∑ a, ∑ b, (r a b : ℤ) * ((if i = a then 1 else 0) - (if i = b then 1 else 0))

def IoPiExists (D : D7) : Prop :=
  ∀ (θ : InfFam D) (V W : HSp D) {S' : D.what₂.Tau → SPar} (M : DSModel W S') (c : CoefA V)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (ap am : D.what₂.Tau → ℕ → ℕ),
    IsInfFam θ → (∀ τ, (gramAt D V τ).PosDef) → 2 * a = (V.rank : ℤ) → Odd W.rank →
    (∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) → c.Is →
    (∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) V.rank (-(e τ : ℚ)) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ))) →
    CoefLowWt θ V BV c (nuDelta V.rank W.rank p e ap am) →
    IoPi θ V W M c BV p a e (delta p (fun τ => W.rank - p τ) ap am)

def FockEquivOfReal (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ),
    IsStdChar D ψ (-1) → RealAtO ψ S T χS χT om → FockEquiv ψ θ S T χS χT om sS sT BS BT p a e

open Formalism.IndefR.FockModel₂ in

def IoPiFromHW (D : D7) : Prop :=
  ∀ (θ : InfFam D) (V W : HSp D) {S' : D.what₂.Tau → SPar} (M : DSModel W S') (c : CoefA V)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (Δ : PolF D W.rank V.rank),
    IsInfFam θ → (∀ τ, (gramAt D V τ).PosDef) → 2 * a = (V.rank : ℤ) → Odd W.rank →
    (∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) → c.Is →
    (∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) V.rank (-(e τ : ℚ)) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ))) →
    CoefLowWt θ V BV c (nuDelta V.rank W.rank p e ap am) →
    Δ ≠ 0 →
    (∀ (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (W.rank - p τ) → ℂ) (t : D.what₂.Tau → Fin V.rank → ℂ),
      (∀ τ i, ‖t₁ τ i‖ = 1) → (∀ τ j, ‖t₂ τ j‖ = 1) → (∀ τ i, ‖t τ i‖ = 1) →
      piAct p a e (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ)) Δ =
        (∏ τ, (∏ i, t₁ τ i ^ ((ap τ i : ℤ) + a - e τ)) * (∏ j, t₂ τ j ^ (-(am τ j : ℤ) - a - e τ)) *
          ∏ i, t τ i ^ nuDelta V.rank W.rank p e ap am τ i) • Δ) →
    (∀ (u₁ : complexSquareMatrixFamily D p) (u₂ : complementBlockMatrixFamily D W.rank p) (u : HFam D V.rank), (∀ τ, IsUpperUni (u₁ τ)) →
      (∀ τ, IsUpperUni (u₂ τ)) → (∀ τ, IsLowerUni (u τ)) → piAct p a e u₁ u₂ u Δ = Δ) →
    IoPi θ V W M c BV p a e Δ

section Lemmas

theorem le_card_of_antitone {f : ℕ → ℕ} (hf : Antitone f) {i L : ℕ} (hi : i < L) (h : f i ≠ 0) :
    i + 1 ≤ ((Finset.range L).filter (fun j => f j ≠ 0)).card := by
  have hsub : Finset.range (i + 1) ⊆ (Finset.range L).filter (fun j => f j ≠ 0) := by
    intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    refine ⟨by omega, ?_⟩
    have := hf (show j ≤ i by omega)
    omega
  simpa using Finset.card_le_card hsub

variable {m n : ℕ}

theorem minorPlus_ne_zero (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun x : FVar D m n =>
    if x.1 = τ ∧ (x.2.1 : ℕ) = x.2.2 then (1 : ℂ) else 0)) h0
  rw [minorPlus, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval (fun x : FVar D m n =>
      if x.1 = τ ∧ (x.2.1 : ℕ) = x.2.2 then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ β α : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hr : (β : ℕ) < m ∧ (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, true_and, Fin.ext_iff, eq_comm]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem minorMinus_ne_zero (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun x : FVar D m n =>
    if x.1 = τ ∧ (x.2.1 : ℕ) + (n - k) = (x.2.2 : ℕ) + p then (1 : ℂ) else 0)) h0
  rw [minorMinus, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval (fun x : FVar D m n =>
      if x.1 = τ ∧ (x.2.1 : ℕ) + (n - k) = (x.2.2 : ℕ) + p then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (p + β) (n - k + α) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hr : p + (β : ℕ) < m ∧ n - k + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, true_and]
    by_cases hab : α = β
    · subst hab; simp only [if_true]; rw [if_pos (by omega)]
    · rw [if_neg hab, if_neg]
      intro h; apply hab; apply Fin.ext; omega
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem delta_ne_zero (p : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hp : ∀ τ, p τ ≤ m)
    (hap : ∀ τ, Antitone (ap τ)) (ham : ∀ τ, Antitone (am τ))
    (hcard : ∀ τ, ((Finset.range (p τ)).filter (fun i => ap τ i ≠ 0)).card +
      ((Finset.range (m - p τ)).filter (fun b => am τ b ≠ 0)).card ≤ n) :
    (delta p (fun τ => m - p τ) ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
  unfold deltaAt
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi => ?_) (Finset.prod_ne_zero_iff.mpr fun i hi => ?_)
  · rw [Finset.mem_range] at hi
    by_cases h0 : ap τ i - (if i + 1 < p τ then ap τ (i + 1) else 0) = 0
    · rw [h0, pow_zero]; exact one_ne_zero
    · have hne : ap τ i ≠ 0 := by omega
      have := le_card_of_antitone (hap τ) hi hne
      have := hcard τ
      exact pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) (by have := hp τ; omega) (by omega))
  · simp only [Finset.mem_range] at hi
    by_cases h0 : am τ i - (if i + 1 < m - p τ then am τ (i + 1) else 0) = 0
    · rw [h0, pow_zero]; exact one_ne_zero
    · have hne : am τ i ≠ 0 := by omega
      have := le_card_of_antitone (ham τ) hi hne
      have := hcard τ
      exact pow_ne_zero _ (minorMinus_ne_zero τ (p τ) (i + 1) (by have := hp τ; omega) (by omega))

theorem offdiag_zero (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (k : Matrix (Fin m) (Fin m) ℂ)
    (hk : k * sgnDiag p τ = sgnDiag p τ * k) (i j : Fin m) (hij : ((i : ℕ) < p τ ↔ ¬ (j : ℕ) < p τ)) : k i j = 0 := by
  have h := congrFun (congrFun hk i) j
  rw [sgnDiag, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_cases hi : (i : ℕ) < p τ
  · have hj : ¬ (j : ℕ) < p τ := hij.mp hi
    rw [if_pos hi, if_neg hj] at h
    linear_combination (-1 / 2 : ℂ) * h
  · have hj : (j : ℕ) < p τ := by by_contra hj; exact hi (hij.mpr hj)
    rw [if_neg hi, if_pos hj] at h
    linear_combination (1 / 2 : ℂ) * h

theorem block_diagonal_of_blocks_eq (p : D.what₂.Tau → ℕ) (kk : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (hk : ∀ τ, kk τ * sgnDiag p τ = sgnDiag p τ * kk τ) (τ : D.what₂.Tau) :
    blockDiagonalOfBlocks p (blk1 p kk) (blk2 p kk) τ = kk τ := by
  ext i j
  have hi' := i.isLt
  have hj' := j.isLt
  simp only [blockDiagonalOfBlocks, blk1, blk2, Matrix.of_apply]
  by_cases hi : (i : ℕ) < p τ <;> by_cases hj : (j : ℕ) < p τ
  · rw [dif_pos hi, dif_pos hj, dif_pos ⟨hi', hj'⟩]
  · rw [dif_pos hi, dif_neg hj]
    exact (offdiag_zero p τ (kk τ) (hk τ) i j ⟨fun _ => hj, fun _ => hi⟩).symm
  · rw [dif_neg hi, dif_pos hj]
    exact (offdiag_zero p τ (kk τ) (hk τ) i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩).symm
  · rw [dif_neg hi, dif_neg hj]
    congr 1 <;> apply Fin.ext <;> simp only <;> omega

end Lemmas

section Transfer

variable {m : ℕ}

theorem first_diagonal_block_unitary (p : D.what₂.Tau → ℕ) (hp : ∀ τ, p τ ≤ m) (kk : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (hk : ∀ τ, kk τ * sgnDiag p τ = sgnDiag p τ * kk τ) (hu : ∀ τ, kk τ ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (τ : D.what₂.Tau) : blk1 p kk τ ∈ Matrix.unitaryGroup (Fin (p τ)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hK := Matrix.mem_unitaryGroup_iff'.mp (hu τ)
  have hpm := hp τ
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  set g : ℕ → ℂ := fun l => if h : l < m then
    star (kk τ ⟨l, h⟩ ⟨i, by omega⟩) * kk τ ⟨l, h⟩ ⟨j, by omega⟩ else 0 with hg
  have e1 : (star (blk1 p kk τ) * blk1 p kk τ) i j = ∑ l ∈ Finset.range (p τ), g l := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := l.isLt
    simp [hg, blk1, Matrix.star_apply, show (l : ℕ) < m by omega, show (i : ℕ) < m by omega,
      show (j : ℕ) < m by omega]
  have e2 : (star (kk τ) * kk τ) ⟨i, by omega⟩ ⟨j, by omega⟩ = ∑ l ∈ Finset.range m, g l := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hg, Matrix.star_apply, l.isLt]
  have e3 : ∑ l ∈ Finset.range (p τ), g l = ∑ l ∈ Finset.range m, g l := by
    refine Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)) fun l hl hnot => ?_
    rw [Finset.mem_range] at hl hnot
    have h0 := offdiag_zero p τ (kk τ) (hk τ) ⟨l, hl⟩ ⟨i, by omega⟩
      ⟨fun h => absurd h (by omega), fun h => absurd hi (by simpa using h)⟩
    simp [hg, hl, h0]
  rw [e1, e3, ← e2, hK]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem second_diagonal_block_unitary (p : D.what₂.Tau → ℕ) (hp : ∀ τ, p τ ≤ m) (kk : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (hk : ∀ τ, kk τ * sgnDiag p τ = sgnDiag p τ * kk τ) (hu : ∀ τ, kk τ ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (τ : D.what₂.Tau) : blk2 p kk τ ∈ Matrix.unitaryGroup (Fin (m - p τ)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hK := Matrix.mem_unitaryGroup_iff'.mp (hu τ)
  have hpm := hp τ
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  set g : ℕ → ℂ := fun l => if h : l < m then
    star (kk τ ⟨l, h⟩ ⟨p τ + i, by omega⟩) * kk τ ⟨l, h⟩ ⟨p τ + j, by omega⟩ else 0 with hg
  have e1 : (star (blk2 p kk τ) * blk2 p kk τ) i j = ∑ l ∈ Finset.range (m - p τ), g (p τ + l) := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range (fun l => g (p τ + l))]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := l.isLt
    simp [hg, blk2, Matrix.star_apply, show p τ + (l : ℕ) < m by omega]
  have e2 : (star (kk τ) * kk τ) ⟨p τ + i, by omega⟩ ⟨p τ + j, by omega⟩ = ∑ l ∈ Finset.range m, g l := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hg, Matrix.star_apply, l.isLt]
  have e3 : ∑ l ∈ Finset.range m, g l = ∑ l ∈ Finset.range (m - p τ), g (p τ + l) := by
    have hs := Finset.sum_range_add g (p τ) (m - p τ)
    rw [show p τ + (m - p τ) = m by omega] at hs
    rw [hs, Finset.sum_eq_zero, zero_add]
    intro l hl
    rw [Finset.mem_range] at hl
    have h0 := offdiag_zero p τ (kk τ) (hk τ) ⟨l, by omega⟩ ⟨p τ + i, by omega⟩
      ⟨fun _ => show ¬ (p τ + (i : ℕ) < p τ) by omega, fun _ => show l < p τ from hl⟩
    simp [hg, show l < m by omega, h0]
  rw [e1, ← e3, ← e2, hK]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem extendOne_one (p : D.what₂.Tau → ℕ) (hp : ∀ τ, p τ ≤ m) :
    blk1 p (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) = fun _ => 1 := by
  funext τ
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have := hp τ
  simp [blk1, Matrix.one_apply, Fin.ext_iff, show (i : ℕ) < m by omega, show (j : ℕ) < m by omega]

theorem symmetricScalarBlockMatrix_one_zero (p : D.what₂.Tau → ℕ) :
    blk2 p (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) = fun _ => 1 := by
  funext τ
  ext i j
  simp [blk2, Matrix.one_apply, Fin.ext_iff]

theorem kAt_self (τ : D.what₂.Tau) (k : Matrix (Fin m) (Fin m) ℂ) : kAt τ k τ = k := by
  simp [kAt]

theorem kAt_ne {τ τ' : D.what₂.Tau} (k : Matrix (Fin m) (Fin m) ℂ) (h : τ' ≠ τ) : kAt τ k τ' = 1 := by
  classical
  unfold kAt
  exact Function.update_of_ne h _ _

theorem jm_eq_sgnDiag (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (ε : Fin m → Bool)
    (hε : ∀ i, ε i = decide ((i : ℕ) < p τ)) : Formalism.REAL.Jm ε = sgnDiag p τ := by
  unfold Formalism.REAL.Jm sgnDiag
  congr 1
  funext i
  simp [hε i]

theorem kAt_props (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (ε : Fin m → Bool) (hε : ∀ i, ε i = decide ((i : ℕ) < p τ))
    (k : Matrix (Fin m) (Fin m) ℂ) (hk : k ∈ Formalism.REAL.Kset ε) (τ' : D.what₂.Tau) :
    kAt τ k τ' * sgnDiag p τ' = sgnDiag p τ' * kAt τ k τ' ∧ kAt τ k τ' ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  by_cases e : τ' = τ
  · subst e
    rw [kAt_self, ← jm_eq_sgnDiag p τ' ε hε]
    exact ⟨hk.2, hk.1⟩
  · rw [kAt_ne k e]
    exact ⟨by rw [Matrix.one_mul, Matrix.mul_one], one_mem _⟩

end Transfer

section Elems

variable {V W : HSp D} {S' : D.what₂.Tau → SPar}

theorem infMat_one' {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) (1 : GA D V) = 1 := by
  have h := Formalism.IndefR.Eqv.isAtTau_atH D V τ 1 (Formalism.IndefR.Eqv.unitary_one D V τ)
  rw [Formalism.IndefR.Eqv.atH_one] at h
  rw [Formalism.IndefR.Eqv.eq_thetaC D hθ]
  exact h.2.1

theorem hOf_unitary {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hBV : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1)
    (u : GA D V) (τ : D.what₂.Tau) : hOf θ V BV u τ ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hX : (infMat D.sp.cm.sig V.gram (θ τ) u)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) u =
      gramAt D V τ := by
    rw [Formalism.IndefR.Eqv.eq_thetaC D hθ]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V u τ
  have hunit : IsUnit (BV τ).det := Matrix.isUnit_det_of_left_inverse (hBV τ)
  have hinv : (BV τ)⁻¹ = (BV τ)ᴴ * gramAt D V τ := Matrix.inv_eq_left_inv (hBV τ)
  have hG : (gramAt D V τ)ᴴ = gramAt D V τ := (hV τ).1
  have hright0 : BV τ * ((BV τ)ᴴ * gramAt D V τ) = 1 := by
    rw [← hinv, Matrix.mul_nonsing_inv _ hunit]
  set X := infMat D.sp.cm.sig V.gram (θ τ) u
  have hh : hOf θ V BV u τ = (BV τ)ᴴ * gramAt D V τ * X * BV τ := by simp only [hOf, hinv, X]
  rw [hh]
  calc ((BV τ)ᴴ * gramAt D V τ * X * BV τ)ᴴ * ((BV τ)ᴴ * gramAt D V τ * X * BV τ)
      = (BV τ)ᴴ * Xᴴ * gramAt D V τ * (BV τ * ((BV τ)ᴴ * gramAt D V τ)) * X * BV τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
    _ = (BV τ)ᴴ * (Xᴴ * gramAt D V τ * X) * BV τ := by
        rw [hright0]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hX, hBV τ]

theorem isInfEl_hOf (θ : InfFam D) (V : HSp D) (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsUnit (BV τ).det) (u : GA D V) (hu : u ∈ GinfC V) :
    IsInfEl θ V (fun τ => BV τ * hOf θ V BV u τ * (BV τ)⁻¹) u := by
  refine ⟨hu, fun τ => ?_⟩
  simp only [hOf, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hB τ), Matrix.mul_nonsing_inv _ (hB τ),
    Matrix.mul_one]

theorem isInfEl_one {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsUnit (B τ).det) : IsInfEl θ V (fun τ => B τ * 1 * (B τ)⁻¹) 1 := by
  refine ⟨one_mem _, fun τ => ?_⟩
  beta_reduce
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ (hB τ), infMat_one' hθ V τ]

theorem isInfEl_atTau {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : gᴴ * gramAt D W τ * g = gramAt D W τ)
    (G : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hG : G τ = g) (hG' : ∀ τ', τ' ≠ τ → G τ' = 1) :
    IsInfEl θ W G (atTau θ W τ g) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  rw [Formalism.IndefR.Eqv.atTau_eq D W τ g hg]
  have h := Formalism.IndefR.Eqv.isAtTau_atH D W τ g hg
  refine ⟨h.1, fun τ' => ?_⟩
  by_cases e : τ' = τ
  · subst e; rw [h.2.1, hG]
  · rw [h.2.2 τ' e, hG' τ' e]

theorem isUnit_fr (M : DSModel W S') (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)

theorem cart_isCartanInv (M : DSModel W S') (τ : D.what₂.Tau) : IsCartanInv (gramAt D W τ) (cart M τ) := by
  have hu := isUnit_fr M τ
  have hJJ : ∀ Y, Formalism.REAL.Jm (M.ε τ) * (Formalism.REAL.Jm (M.ε τ) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]
  have hJh : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : M.ε τ a <;> simp [h]
  have hFF : ∀ Y, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [← M.fr_gram τ]
  unfold cart
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hJJ, Matrix.nonsing_inv_mul _ hu]
  · simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hFF, hJJ]
  · have e : (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) =
        (M.fr τ)ᴴ * M.fr τ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hJJ]
    rw [e]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have h2 := congrArg ((M.fr τ)⁻¹).mulVec hxy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using h2

theorem onb_props (M : DSModel W S') (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau)
    (hε : ∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) :
    (onb M τ)ᴴ * gramAt D W τ * onb M τ = sgnDiag p τ ∧ cart M τ * onb M τ = onb M τ * sgnDiag p τ := by
  have hu := isUnit_fr M τ
  have hFF : ∀ Y, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [← jm_eq_sgnDiag p τ (M.ε τ) hε, ← M.fr_gram τ]
  unfold onb cart
  constructor
  · simp only [Matrix.mul_assoc, hFF, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem frk_unitary (M : DSModel W S') (τ : D.what₂.Tau) (k : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D W τ := by
  have hu := isUnit_fr M τ
  have hFF : ∀ Y, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hkk : ∀ Y, kᴴ * (k * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hk.1, Matrix.one_mul]
  have hJk : ∀ Y, Formalism.REAL.Jm (M.ε τ) * (k * Y) = k * (Formalism.REAL.Jm (M.ε τ) * Y) := by
    intro Y; rw [← Matrix.mul_assoc, ← hk.2, Matrix.mul_assoc]
  rw [← M.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hFF, hJk, hkk]

end Elems

section Extremal

variable {m n : ℕ}

def dScal (p : D.what₂.Tau → ℕ) (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ)
    (x : FVar D m n) : ℂ :=
  if h : (x.2.1 : ℕ) < p x.1 then (t x.1 x.2.2)⁻¹ * t₁ x.1 ⟨x.2.1, h⟩
  else t x.1 x.2.2 * starRingEnd ℂ (t₂ x.1 ⟨(x.2.1 : ℕ) - p x.1, by have := x.2.1.isLt; omega⟩)

theorem inv_diagonal' {k : ℕ} (v : Fin k → ℂ) (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal fun i => (v i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext i
  exact inv_mul_cancel₀ (hv i)

theorem substVar_diag (p : D.what₂.Tau → ℕ) (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ)
    (t : D.what₂.Tau → Fin n → ℂ) (ht : ∀ τ c, t τ c ≠ 0) (x : FVar D m n) :
    substVar p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ)) x =
      MvPolynomial.C (dScal p t₁ t₂ t x) * MvPolynomial.X x := by
  obtain ⟨τ, i, c⟩ := x
  have hi' := i.isLt
  have hc' := c.isLt
  unfold substVar dScal
  by_cases hi : (i : ℕ) < p τ
  · simp only [dif_pos hi, zPlusS, zPlus, inv_diagonal' _ (ht τ), Matrix.diagonal_map (map_zero _),
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, varF, dif_pos (⟨hi', hc'⟩ : (i : ℕ) < m ∧ (c : ℕ) < n)]
    rw [MvPolynomial.C_mul]
    ring
  · have hq : (i : ℕ) - p τ < m - p τ := by omega
    have he : (⟨p τ + ((i : ℕ) - p τ), by omega⟩ : Fin m) = i := Fin.ext (by simp only; omega)
    have hm : (Matrix.diagonal (t₂ τ)).map (fun x : ℂ => (MvPolynomial.C (starRingEnd ℂ x) : MvPolynomial (FVar D m n) ℂ)) =
        Matrix.diagonal fun j => MvPolynomial.C (starRingEnd ℂ (t₂ τ j)) := Matrix.diagonal_map (by simp)
    simp only [dif_neg hi, zMinusS, zMinus, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), hm]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, varF, dif_pos (⟨by omega, hc'⟩ : p τ + ((i : ℕ) - p τ) < m ∧ (c : ℕ) < n), he]
    rw [MvPolynomial.C_mul]
    ring

def rowP (t : D.what₂.Tau → Fin n → ℂ) (τ : D.what₂.Tau) (α : ℕ) : ℂ := if h : α < n then (t τ ⟨α, h⟩)⁻¹ else 1

def colP (p : D.what₂.Tau → ℕ) (t₁ : ∀ τ, Fin (p τ) → ℂ) (τ : D.what₂.Tau) (β : ℕ) : ℂ :=
  if h : β < p τ then t₁ τ ⟨β, h⟩ else 1

def rowM (t : D.what₂.Tau → Fin n → ℂ) (τ : D.what₂.Tau) (r : ℕ) : ℂ := if h : r < n then t τ ⟨n - 1 - r, by omega⟩ else 1

def colM (p : D.what₂.Tau → ℕ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (τ : D.what₂.Tau) (β : ℕ) : ℂ :=
  if h : β < m - p τ then starRingEnd ℂ (t₂ τ ⟨β, h⟩) else 1

theorem polySubst_diag_minorPlus (p : D.what₂.Tau → ℕ) (hpm : ∀ τ, p τ ≤ m) (t₁ : ∀ τ, Fin (p τ) → ℂ)
    (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ) (ht : ∀ τ c, t τ c ≠ 0) (τ : D.what₂.Tau) (k : ℕ)
    (hkp : k ≤ p τ) :
    polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) =
      MvPolynomial.C ((∏ α ∈ Finset.range k, rowP t τ α) * ∏ β ∈ Finset.range k, colP p t₁ τ β) * minorPlus τ k := by
  unfold minorPlus
  rw [AlgHom.map_det]
  have hA : (polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ))
      (fun τ => Matrix.diagonal (t τ))).mapMatrix
        (Matrix.of fun α β : Fin k => (varF τ β α : MvPolynomial (FVar D m n) ℂ)) =
      Matrix.diagonal (fun α : Fin k => MvPolynomial.C (rowP t τ α)) *
        (Matrix.of fun α β : Fin k => (varF τ β α : MvPolynomial (FVar D m n) ℂ)) *
        Matrix.diagonal (fun β : Fin k => MvPolynomial.C (colP p t₁ τ β)) := by
    ext α β
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hβ : (β : ℕ) < p τ := by have := β.isLt; omega
    have hβm : (β : ℕ) < m := by have := hpm τ; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF]
    by_cases hα : (α : ℕ) < n
    · rw [dif_pos ⟨hβm, hα⟩, polySubst_X, substVar_diag _ _ _ _ ht]
      simp only [dScal, dif_pos hβ, rowP, colP, dif_pos hα, MvPolynomial.C_mul]
      ring
    · rw [dif_neg (fun h => hα h.2)]
      simp
  rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, ← map_prod, ← map_prod,
    Fin.prod_univ_eq_prod_range (rowP t τ) k, Fin.prod_univ_eq_prod_range (colP p t₁ τ) k, MvPolynomial.C_mul]
  ring

theorem polySubst_diag_minorMinus (p : D.what₂.Tau → ℕ) (t₁ : ∀ τ, Fin (p τ) → ℂ)
    (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ) (ht : ∀ τ c, t τ c ≠ 0) (τ : D.what₂.Tau) (k : ℕ)
    (hkn : k ≤ n) (hkm : p τ + k ≤ m) :
    polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        (minorMinus τ (p τ) k : MvPolynomial (FVar D m n) ℂ) =
      MvPolynomial.C ((∏ r ∈ Finset.range k, rowM t τ r) * ∏ β ∈ Finset.range k, colM p t₂ τ β) *
        minorMinus τ (p τ) k := by
  unfold minorMinus
  rw [AlgHom.map_det]
  have hA : (polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ))
      (fun τ => Matrix.diagonal (t τ))).mapMatrix
        (Matrix.of fun α β : Fin k => (varF τ (p τ + β) (n - k + α) : MvPolynomial (FVar D m n) ℂ)) =
      Matrix.diagonal (fun α : Fin k => MvPolynomial.C (rowM t τ (k - 1 - α))) *
        (Matrix.of fun α β : Fin k => (varF τ (p τ + β) (n - k + α) : MvPolynomial (FVar D m n) ℂ)) *
        Matrix.diagonal (fun β : Fin k => MvPolynomial.C (colM p t₂ τ β)) := by
    ext α β
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hα := α.isLt
    have hβ := β.isLt
    have hr : p τ + (β : ℕ) < m ∧ n - k + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr]
    rw [polySubst_X, substVar_diag _ _ _ _ ht]
    have hnp : ¬ (p τ + (β : ℕ) < p τ) := by omega
    have hq : (β : ℕ) < m - p τ := by omega
    have hk1 : k - 1 - (α : ℕ) < n := by omega
    have hidx : (⟨n - 1 - (k - 1 - (α : ℕ)), by omega⟩ : Fin n) = ⟨n - k + α, hr.2⟩ := Fin.ext (by simp only; omega)
    have hidx2 : (⟨p τ + (β : ℕ) - p τ, by omega⟩ : Fin (m - p τ)) = ⟨β, hq⟩ := Fin.ext (by simp only; omega)
    simp only [dScal, dif_neg hnp, rowM, colM, dif_pos hk1, dif_pos hq, hidx, hidx2, MvPolynomial.C_mul]
    ring
  rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, ← map_prod, ← map_prod,
    Fin.prod_univ_eq_prod_range (fun α => rowM t τ (k - 1 - α)) k, Fin.prod_univ_eq_prod_range (colM p t₂ τ) k,
    Finset.prod_range_reflect (rowM t τ) k, MvPolynomial.C_mul]
  ring

theorem prod_telescope {M : Type*} [CommMonoid M] (g : ℕ → M) (f : ℕ → ℕ) (hf : Antitone f) (P : ℕ) :
    (∏ i ∈ Finset.range P, (∏ α ∈ Finset.range (i + 1), g α) ^ (f i - f (i + 1))) *
        (∏ α ∈ Finset.range P, g α) ^ f P = ∏ α ∈ Finset.range P, g α ^ f α := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.prod_range_succ (fun α => g α ^ f α), ← ih, Finset.prod_range_succ, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (hf (Nat.le_succ P)), Finset.prod_range_succ g P, mul_pow, mul_assoc]

theorem prod_telescope' {M : Type*} [CommMonoid M] (g : ℕ → M) (f : ℕ → ℕ) (hf : Antitone f) (P : ℕ)
    (h0 : ∀ i, P ≤ i → f i = 0) :
    ∏ i ∈ Finset.range P, (∏ α ∈ Finset.range (i + 1), g α) ^ (f i - if i + 1 < P then f (i + 1) else 0) =
      ∏ α ∈ Finset.range P, g α ^ f α := by
  rw [← prod_telescope g f hf P, h0 P le_rfl, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i hi => ?_
  split_ifs with h
  · rfl
  · rw [h0 (i + 1) (by omega)]

theorem polySubst_diag_deltaAt (p : D.what₂.Tau → ℕ) (hpm : ∀ τ, p τ ≤ m) (t₁ : ∀ τ, Fin (p τ) → ℂ)
    (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ) (ht : ∀ τ c, t τ c ≠ 0) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hap : ∀ τ, Antitone (ap τ)) (ham : ∀ τ, Antitone (am τ)) (hap0 : ∀ τ i, p τ ≤ i → ap τ i = 0)
    (ham0 : ∀ τ b, m - p τ ≤ b → am τ b = 0)
    (hcard : ∀ τ, ((Finset.range (p τ)).filter (fun i => ap τ i ≠ 0)).card +
      ((Finset.range (m - p τ)).filter (fun b => am τ b ≠ 0)).card ≤ n) (τ : D.what₂.Tau) :
    polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        (deltaAt τ (p τ) (ap τ) (m - p τ) (am τ) : MvPolynomial (FVar D m n) ℂ) =
      MvPolynomial.C ((∏ α ∈ Finset.range (p τ), (rowP t τ α * colP p t₁ τ α) ^ ap τ α) *
        ∏ r ∈ Finset.range (m - p τ), (rowM t τ r * colM p t₂ τ r) ^ am τ r) *
        deltaAt τ (p τ) (ap τ) (m - p τ) (am τ) := by
  unfold deltaAt
  rw [map_mul, map_prod, map_prod]
  have hplus : ∀ i ∈ Finset.range (p τ),
      polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        ((minorPlus τ (i + 1) : MvPolynomial (FVar D m n) ℂ) ^ (ap τ i - if i + 1 < p τ then ap τ (i + 1) else 0)) =
      MvPolynomial.C ((∏ α ∈ Finset.range (i + 1), (rowP t τ α * colP p t₁ τ α)) ^
          (ap τ i - if i + 1 < p τ then ap τ (i + 1) else 0)) *
        (minorPlus τ (i + 1) : MvPolynomial (FVar D m n) ℂ) ^ (ap τ i - if i + 1 < p τ then ap τ (i + 1) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_pow, polySubst_diag_minorPlus p hpm t₁ t₂ t ht τ (i + 1) (by omega), mul_pow, ← map_pow,
      Finset.prod_mul_distrib]
  have hminus : ∀ i ∈ Finset.range (m - p τ),
      polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        ((minorMinus τ (p τ) (i + 1) : MvPolynomial (FVar D m n) ℂ) ^
          (am τ i - if i + 1 < m - p τ then am τ (i + 1) else 0)) =
      MvPolynomial.C ((∏ r ∈ Finset.range (i + 1), (rowM t τ r * colM p t₂ τ r)) ^
          (am τ i - if i + 1 < m - p τ then am τ (i + 1) else 0)) *
        (minorMinus τ (p τ) (i + 1) : MvPolynomial (FVar D m n) ℂ) ^
          (am τ i - if i + 1 < m - p τ then am τ (i + 1) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h0 : am τ i - (if i + 1 < m - p τ then am τ (i + 1) else 0) = 0
    · rw [h0]; simp
    · have hne : am τ i ≠ 0 := by omega
      have := le_card_of_antitone (ham τ) hi hne
      have := hcard τ
      rw [map_pow, polySubst_diag_minorMinus p t₁ t₂ t ht τ (i + 1) (by omega) (by have := hpm τ; omega), mul_pow,
        ← map_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl hplus, Finset.prod_congr rfl hminus, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← map_prod, ← map_prod,
    prod_telescope' (fun α => rowP t τ α * colP p t₁ τ α) (ap τ) (hap τ) (p τ) (hap0 τ),
    prod_telescope' (fun r => rowM t τ r * colM p t₂ τ r) (am τ) (ham τ) (m - p τ) (ham0 τ), MvPolynomial.C_mul]
  ring

theorem prod_range_trunc {M : Type*} [CommMonoid M] (f : ℕ → M) {A L : ℕ} (hL : L ≤ A)
    (h1 : ∀ α, L ≤ α → α < A → f α = 1) : ∏ α ∈ Finset.range A, f α = ∏ α ∈ Finset.range L, f α := by
  refine (Finset.prod_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)) fun α hA hL' => ?_).symm
  rw [Finset.mem_range] at hA hL'
  exact h1 α (by omega) hA

theorem zero_of_card {f : ℕ → ℕ} (hf : Antitone f) {L n : ℕ}
    (hc : ((Finset.range L).filter (fun i => f i ≠ 0)).card ≤ n) (h0 : ∀ i, L ≤ i → f i = 0) :
    ∀ i, n ≤ i → f i = 0 := by
  intro i hi
  by_contra h
  by_cases hiL : i < L
  · have := le_card_of_antitone hf hiL h
    omega
  · exact h (h0 i (by omega))

theorem scal_id (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ) (t₁ : ∀ τ, Fin (p τ) → ℂ)
    (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ) (h1 : ∀ τ i, t₁ τ i ≠ 0)
    (h2 : ∀ τ j, ‖t₂ τ j‖ = 1) (h3 : ∀ τ c, t τ c ≠ 0) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hap : ∀ τ, Antitone (ap τ)) (ham : ∀ τ, Antitone (am τ)) (hap0 : ∀ τ i, p τ ≤ i → ap τ i = 0)
    (ham0 : ∀ τ b, m - p τ ≤ b → am τ b = 0)
    (hcard : ∀ τ, ((Finset.range (p τ)).filter (fun i => ap τ i ≠ 0)).card +
      ((Finset.range (m - p τ)).filter (fun b => am τ b ≠ 0)).card ≤ n) (τ : D.what₂.Tau) :
    (∏ i, t₁ τ i) ^ (a - e τ) * (∏ j, t₂ τ j) ^ (-a - e τ) * (∏ c, t τ c) ^ (-dExp m p e τ) *
        ((∏ α ∈ Finset.range (p τ), (rowP t τ α * colP p t₁ τ α) ^ ap τ α) *
          ∏ r ∈ Finset.range (m - p τ), (rowM t τ r * colM p t₂ τ r) ^ am τ r) =
      (∏ i, t₁ τ i ^ ((ap τ i : ℤ) + a - e τ)) * (∏ j, t₂ τ j ^ (-(am τ j : ℤ) - a - e τ)) *
        ∏ c, t τ c ^ nuDelta n m p e ap am τ c := by
  have hapn := zero_of_card (hap τ) (le_trans (Nat.le_add_right _ _) (hcard τ)) (hap0 τ)
  have hamn := zero_of_card (ham τ) (le_trans (Nat.le_add_left _ _) (hcard τ)) (ham0 τ)
  have s1 : ∏ α ∈ Finset.range (p τ), colP p t₁ τ α ^ ap τ α = ∏ i : Fin (p τ), t₁ τ i ^ ap τ i := by
    rw [← Fin.prod_univ_eq_prod_range (fun α => colP p t₁ τ α ^ ap τ α)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [colP, i.isLt]
  have s2 : ∏ α ∈ Finset.range (p τ), rowP t τ α ^ ap τ α = ∏ c : Fin n, (t τ c)⁻¹ ^ ap τ c := by
    rw [prod_range_trunc (fun α => rowP t τ α ^ ap τ α) (min_le_left (p τ) n)
        (fun α h _ => by rw [(min_le_iff.mp h).elim (hap0 τ α) (hapn α), pow_zero]),
      ← prod_range_trunc (fun α => rowP t τ α ^ ap τ α) (min_le_right (p τ) n)
        (fun α h _ => by rw [(min_le_iff.mp h).elim (hap0 τ α) (hapn α), pow_zero]),
      ← Fin.prod_univ_eq_prod_range (fun α => rowP t τ α ^ ap τ α)]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp [rowP, c.isLt]
  have s3 : ∏ r ∈ Finset.range (m - p τ), colM p t₂ τ r ^ am τ r = ∏ j : Fin (m - p τ), (t₂ τ j)⁻¹ ^ am τ j := by
    rw [← Fin.prod_univ_eq_prod_range (fun r => colM p t₂ τ r ^ am τ r)]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [colM, j.isLt, Complex.inv_eq_conj (h2 τ j)]
  have s4 : ∏ r ∈ Finset.range (m - p τ), rowM t τ r ^ am τ r = ∏ c : Fin n, t τ c ^ am τ (n - 1 - c) := by
    rw [prod_range_trunc (fun r => rowM t τ r ^ am τ r) (min_le_left (m - p τ) n)
        (fun α h _ => by rw [(min_le_iff.mp h).elim (ham0 τ α) (hamn α), pow_zero]),
      ← prod_range_trunc (fun r => rowM t τ r ^ am τ r) (min_le_right (m - p τ) n)
        (fun α h _ => by rw [(min_le_iff.mp h).elim (ham0 τ α) (hamn α), pow_zero]),
      ← Finset.prod_range_reflect (fun r => rowM t τ r ^ am τ r) n,
      ← Fin.prod_univ_eq_prod_range (fun c => rowM t τ (n - 1 - c) ^ am τ (n - 1 - c))]
    refine Finset.prod_congr rfl fun c _ => ?_
    have hc := c.isLt
    have hidx : (⟨n - 1 - (n - 1 - (c : ℕ)), by omega⟩ : Fin n) = c := Fin.ext (by simp only; omega)
    simp only [rowM, dif_pos (show n - 1 - (c : ℕ) < n by omega), hidx]
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [s1, s2, s3, s4]
  have r1 : ∀ i : Fin (p τ), t₁ τ i ^ ((ap τ i : ℤ) + a - e τ) = t₁ τ i ^ (ap τ i) * t₁ τ i ^ (a - e τ) := by
    intro i; rw [add_sub_assoc, zpow_add₀ (h1 τ i), zpow_natCast]
  have r2 : ∀ j : Fin (m - p τ), t₂ τ j ^ (-(am τ j : ℤ) - a - e τ) = (t₂ τ j)⁻¹ ^ (am τ j) * t₂ τ j ^ (-a - e τ) := by
    intro j
    have hj : t₂ τ j ≠ 0 := by intro h; have := h2 τ j; rw [h, norm_zero] at this; exact zero_ne_one this
    rw [show -(am τ j : ℤ) - a - e τ = -(am τ j : ℤ) + (-a - e τ) by ring, zpow_add₀ hj, _root_.zpow_neg, zpow_natCast, inv_pow]
  have r3 : ∀ c : Fin n, t τ c ^ nuDelta n m p e ap am τ c =
      (t τ c)⁻¹ ^ (ap τ c) * t τ c ^ (am τ (n - 1 - c)) * t τ c ^ (-dExp m p e τ) := by
    intro c
    unfold nuDelta
    rw [show -(ap τ c : ℤ) + (am τ (n - 1 - c) : ℤ) - dExp m p e τ =
        -(ap τ c : ℤ) + (am τ (n - 1 - c) : ℤ) + -dExp m p e τ by ring, zpow_add₀ (h3 τ c), zpow_add₀ (h3 τ c),
      _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
  simp only [r1, r2, r3, Finset.prod_mul_distrib, Finset.prod_zpow]
  ring

theorem piAct_diag_delta (p : D.what₂.Tau → ℕ) (hpm : ∀ τ, p τ ≤ m) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ)
    (h1 : ∀ τ i, ‖t₁ τ i‖ = 1) (h2 : ∀ τ j, ‖t₂ τ j‖ = 1) (h3 : ∀ τ c, ‖t τ c‖ = 1) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hap : ∀ τ, Antitone (ap τ)) (ham : ∀ τ, Antitone (am τ)) (hap0 : ∀ τ i, p τ ≤ i → ap τ i = 0)
    (ham0 : ∀ τ b, m - p τ ≤ b → am τ b = 0)
    (hcard : ∀ τ, ((Finset.range (p τ)).filter (fun i => ap τ i ≠ 0)).card +
      ((Finset.range (m - p τ)).filter (fun b => am τ b ≠ 0)).card ≤ n) :
    piAct p a e (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ)) (fun τ => Matrix.diagonal (t τ))
        (delta p (fun τ => m - p τ) ap am : MvPolynomial (FVar D m n) ℂ) =
      (∏ τ, (∏ i, t₁ τ i ^ ((ap τ i : ℤ) + a - e τ)) * (∏ j, t₂ τ j ^ (-(am τ j : ℤ) - a - e τ)) *
        ∏ c, t τ c ^ nuDelta n m p e ap am τ c) • delta p (fun τ => m - p τ) ap am := by
  have ne : ∀ {z : ℂ}, ‖z‖ = 1 → z ≠ 0 := fun hz h => by rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hpoly : polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ))
      (fun τ => Matrix.diagonal (t τ)) (delta p (fun τ => m - p τ) ap am : MvPolynomial (FVar D m n) ℂ) =
      MvPolynomial.C (∏ τ, (∏ α ∈ Finset.range (p τ), (rowP t τ α * colP p t₁ τ α) ^ ap τ α) *
        ∏ r ∈ Finset.range (m - p τ), (rowM t τ r * colM p t₂ τ r) ^ am τ r) * delta p (fun τ => m - p τ) ap am := by
    unfold delta
    rw [map_prod, Finset.prod_congr rfl fun τ _ => polySubst_diag_deltaAt p hpm t₁ t₂ t (fun τ c => ne (h3 τ c)) ap am
      hap ham hap0 ham0 hcard τ, Finset.prod_mul_distrib, ← map_prod]
  unfold piAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, hpoly, MvPolynomial.C_mul', smul_smul]
  congr 1
  unfold fockChar
  simp only [Matrix.det_diagonal]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => scal_id p a e t₁ t₂ t (fun τ i => ne (h1 τ i)) h2 (fun τ c => ne (h3 τ c))
    ap am hap ham hap0 ham0 hcard τ

open Formalism.IndefR.FockModel₂ in

theorem lowerUni_inv {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : IsLowerUni u) : IsLowerUni u⁻¹ := by
  have hbt : u.BlockTriangular OrderDual.toDual := fun i j hij => by
    have := (hu j i).1 (by simpa using hij)
    simpa [Matrix.transpose_apply] using this
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_lowerTriangular u hbt]
    exact Finset.prod_eq_one fun i _ => by have := (hu i i).2 rfl; simpa [Matrix.transpose_apply] using this
  haveI : Invertible u := Matrix.invertibleOfIsUnitDet u (by rw [hdet]; exact isUnit_one)
  have hbt' : u⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular hbt
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · simp only [Matrix.transpose_apply]
    exact hbt' (by simpa using hji)
  · subst hij
    simp only [Matrix.transpose_apply]
    have h1 : (u * u⁻¹) i i = (1 : Matrix (Fin N) (Fin N) ℂ) i i := by
      rw [Matrix.mul_nonsing_inv u (by rw [hdet]; exact isUnit_one)]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · have hii : u i i = 1 := by have := (hu i i).2 rfl; simpa [Matrix.transpose_apply] using this
      rw [hii, one_mul, Matrix.one_apply_eq] at h1
      exact h1
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hbt' (show OrderDual.toDual i < OrderDual.toDual j from h), mul_zero]
      · rw [hbt (show OrderDual.toDual j < OrderDual.toDual i from h), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_fin_trunc {R : Type*} [AddCommMonoid R] {N k : ℕ} (hk : k ≤ N) (f : Fin N → R)
    (hf : ∀ i : Fin N, k ≤ (i : ℕ) → f i = 0) : ∑ i, f i = ∑ j : Fin k, f ⟨j, by omega⟩ := by
  classical
  let g : ℕ → R := fun i => if h : i < N then f ⟨i, h⟩ else 0
  have e1 : ∑ i, f i = ∑ i ∈ Finset.range N, g i := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    exact Finset.sum_congr rfl fun i _ => by simp [g, i.isLt]
  have e2 : ∑ j : Fin k, f ⟨j, by omega⟩ = ∑ i ∈ Finset.range k, g i := by
    rw [← Fin.sum_univ_eq_sum_range g k]
    exact Finset.sum_congr rfl fun j _ => by simp [g, show (j : ℕ) < N by omega]
  rw [e1, e2]
  refine (Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)) fun i hi hni => ?_).symm
  rw [Finset.mem_range] at hi hni
  simp only [g, dif_pos hi]
  exact hf ⟨i, hi⟩ (by simp only; omega)

theorem sum_fin_trunc_top {R : Type*} [AddCommMonoid R] {N k : ℕ} (hk : k ≤ N) (f : Fin N → R)
    (hf : ∀ i : Fin N, (i : ℕ) < N - k → f i = 0) : ∑ i, f i = ∑ j : Fin k, f ⟨N - k + j, by omega⟩ := by
  classical
  let g : ℕ → R := fun i => if h : i < N then f ⟨i, h⟩ else 0
  have e1 : ∑ i, f i = ∑ i ∈ Finset.range N, g i := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    exact Finset.sum_congr rfl fun i _ => by simp [g, i.isLt]
  have e2 : ∑ j : Fin k, f ⟨N - k + j, by omega⟩ = ∑ i ∈ Finset.range k, g (N - k + i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (N - k + i)) k]
    exact Finset.sum_congr rfl fun j _ => by simp [g, show N - k + (j : ℕ) < N by omega]
  rw [e1, e2]
  have hs := Finset.sum_range_add g (N - k) k
  rw [show N - k + k = N by omega] at hs
  rw [hs, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [g, dif_pos (show i < N by omega)]
  exact hf ⟨i, by omega⟩ (by simp only; omega)

open Formalism.IndefR.FockModel₂ in

theorem polySubst_unip_minorPlus (p : D.what₂.Tau → ℕ) (hpm : ∀ τ, p τ ≤ m) (u₁ : complexSquareMatrixFamily D p) (u₂ : complementBlockMatrixFamily D m p)
    (u : HFam D n) (hu₁ : ∀ τ, IsUpperUni (u₁ τ)) (hu : ∀ τ, IsLowerUni (u τ)) (τ : D.what₂.Tau) (k : ℕ)
    (hkp : k ≤ p τ) (hkn : k ≤ n) :
    polySubst p u₁ u₂ u (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) = minorPlus τ k := by
  have hinv := lowerUni_inv (u τ) (hu τ)
  have hpm' := hpm τ
  unfold minorPlus
  rw [AlgHom.map_det]
  set A : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun α β : Fin k => (varF τ β α : MvPolynomial (FVar D m n) ℂ) with hAdef
  set L : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun α γ : Fin k => MvPolynomial.C ((u τ)⁻¹ ⟨α, by omega⟩ ⟨γ, by omega⟩) with hL
  set U : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun δ β : Fin k => MvPolynomial.C (u₁ τ ⟨δ, by omega⟩ ⟨β, by omega⟩) with hU
  have hA : (polySubst p u₁ u₂ u).mapMatrix A = L * A * U := by
    refine Matrix.ext fun α β => ?_
    have hα := α.isLt
    have hβ := β.isLt
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hAdef, Matrix.of_apply, varF,
      dif_pos (⟨by omega, by omega⟩ : (β : ℕ) < m ∧ (α : ℕ) < n), polySubst_X]
    unfold substVar
    rw [dif_pos (show ((⟨β, by omega⟩ : Fin m) : ℕ) < p τ by simp only; omega)]
    unfold zPlusS zPlus
    dsimp only
    rw [Matrix.mul_apply, Matrix.mul_apply, sum_fin_trunc (R := MvPolynomial (FVar D m n) ℂ) (k := k) hkp]
    · refine Finset.sum_congr rfl fun δ _ => ?_
      have hδ := δ.isLt
      rw [Matrix.mul_apply, Matrix.mul_apply, sum_fin_trunc (R := MvPolynomial (FVar D m n) ℂ) (k := k) hkn]
      · rfl
      · intro c hc
        have := (hinv c ⟨α, by omega⟩).1 (show (⟨α, by omega⟩ : Fin n) < c from Fin.lt_def.mpr (by simp only; omega))
        simp only [Matrix.transpose_apply] at this
        simp [Matrix.map_apply, this]
    · intro a' ha'
      have := (hu₁ τ a' ⟨β, by omega⟩).1 (Fin.lt_def.mpr (by simp only; omega))
      simp [Matrix.map_apply, this]
  have hLt : L.BlockTriangular OrderDual.toDual := fun i j hij => by
    have := (hinv ⟨j, by omega⟩ ⟨i, by omega⟩).1 (Fin.lt_def.mpr (by simp only; exact hij))
    simp only [Matrix.transpose_apply] at this
    simp [hL, this]
  have hUt : U.BlockTriangular id := fun i j hij => by
    have := (hu₁ τ ⟨i, by omega⟩ ⟨j, by omega⟩).1 (Fin.lt_def.mpr (by simp only; exact hij))
    simp [hU, this]
  rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_lowerTriangular L hLt, Matrix.det_of_upperTriangular hUt]
  have h1 : ∏ i, L i i = 1 := Finset.prod_eq_one fun i _ => by
    have := (hinv ⟨i, by omega⟩ ⟨i, by omega⟩).2 rfl
    simp only [Matrix.transpose_apply] at this
    simp [hL, this]
  have h2 : ∏ i, U i i = 1 := Finset.prod_eq_one fun i _ => by
    have := (hu₁ τ ⟨i, by omega⟩ ⟨i, by omega⟩).2 rfl
    simp [hU, this]
  rw [h1, h2, one_mul, mul_one]

open Formalism.IndefR.FockModel₂ in

theorem polySubst_unip_minorMinus (p : D.what₂.Tau → ℕ) (u₁ : complexSquareMatrixFamily D p) (u₂ : complementBlockMatrixFamily D m p)
    (u : HFam D n) (hu₂ : ∀ τ, IsUpperUni (u₂ τ)) (hu : ∀ τ, IsLowerUni (u τ)) (τ : D.what₂.Tau) (k : ℕ)
    (hkn : k ≤ n) (hkm : p τ + k ≤ m) :
    polySubst p u₁ u₂ u (minorMinus τ (p τ) k : MvPolynomial (FVar D m n) ℂ) = minorMinus τ (p τ) k := by
  unfold minorMinus
  rw [AlgHom.map_det]
  set A : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun α β : Fin k => (varF τ (p τ + β) (n - k + α) : MvPolynomial (FVar D m n) ℂ) with hAdef
  set L : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun α γ : Fin k => MvPolynomial.C ((u τ)ᵀ ⟨n - k + α, by omega⟩ ⟨n - k + γ, by omega⟩) with hL
  set U : Matrix (Fin k) (Fin k) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.of fun δ β : Fin k => MvPolynomial.C (starRingEnd ℂ (u₂ τ ⟨δ, by omega⟩ ⟨β, by omega⟩)) with hU
  have hA : (polySubst p u₁ u₂ u).mapMatrix A = L * A * U := by
    refine Matrix.ext fun α β => ?_
    have hα := α.isLt
    have hβ := β.isLt
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hAdef, Matrix.of_apply, varF,
      dif_pos (⟨by omega, by omega⟩ : p τ + (β : ℕ) < m ∧ n - k + (α : ℕ) < n), polySubst_X]
    unfold substVar
    rw [dif_neg (show ¬ ((⟨p τ + β, by omega⟩ : Fin m) : ℕ) < p τ by simp only; omega)]
    unfold zMinusS zMinus
    dsimp only
    simp only [Nat.add_sub_cancel_left]
    rw [Matrix.mul_apply, Matrix.mul_apply, sum_fin_trunc (R := MvPolynomial (FVar D m n) ℂ) (k := k) (by omega)]
    · refine Finset.sum_congr rfl fun δ _ => ?_
      have hδ := δ.isLt
      rw [Matrix.mul_apply, Matrix.mul_apply, sum_fin_trunc_top (R := MvPolynomial (FVar D m n) ℂ) (k := k) hkn]
      · rfl
      · intro c hc
        have := (hu τ ⟨n - k + α, by omega⟩ c).1 (Fin.lt_def.mpr (by simp only; omega))
        simp only [Matrix.transpose_apply] at this
        simp [Matrix.map_apply, this]
    · intro b' hb'
      have := (hu₂ τ b' ⟨β, by omega⟩).1 (Fin.lt_def.mpr (by simp only; omega))
      simp [Matrix.map_apply, this]
  have hLt : L.BlockTriangular id := fun i j hij => by
    have := (hu τ ⟨n - k + i, by omega⟩ ⟨n - k + j, by omega⟩).1 (Fin.lt_def.mpr (by simp only [id] at hij ⊢; omega))
    simp only [Matrix.transpose_apply] at this
    simp [hL, this]
  have hUt : U.BlockTriangular id := fun i j hij => by
    have := (hu₂ τ ⟨i, by omega⟩ ⟨j, by omega⟩).1 (Fin.lt_def.mpr (by simp only; exact hij))
    simp [hU, this]
  rw [hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_upperTriangular hLt, Matrix.det_of_upperTriangular hUt]
  have h1 : ∏ i, L i i = 1 := Finset.prod_eq_one fun i _ => by
    have := (hu τ ⟨n - k + i, by omega⟩ ⟨n - k + i, by omega⟩).2 rfl
    simp only [Matrix.transpose_apply] at this
    simp [hL, this]
  have h2 : ∏ i, U i i = 1 := Finset.prod_eq_one fun i _ => by
    have := (hu₂ τ ⟨i, by omega⟩ ⟨i, by omega⟩).2 rfl
    simp [hU, this]
  rw [h1, h2, one_mul, mul_one]

open Formalism.IndefR.FockModel₂ in

theorem det_upperUni {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : IsUpperUni u) : u.det = 1 := by
  have hbt : u.BlockTriangular id := fun i j hij => (hu i j).1 hij
  rw [Matrix.det_of_upperTriangular hbt]
  exact Finset.prod_eq_one fun i _ => (hu i i).2 rfl

open Formalism.IndefR.FockModel₂ in

theorem det_lowerUni {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : IsLowerUni u) : u.det = 1 := by
  rw [← Matrix.det_transpose]; exact det_upperUni _ hu

open Formalism.IndefR.FockModel₂ in

theorem piAct_unip_delta (p : D.what₂.Tau → ℕ) (hpm : ∀ τ, p τ ≤ m) (a : ℤ) (e : D.what₂.Tau → ℤ) (u₁ : complexSquareMatrixFamily D p)
    (u₂ : complementBlockMatrixFamily D m p) (u : HFam D n) (hu₁ : ∀ τ, IsUpperUni (u₁ τ)) (hu₂ : ∀ τ, IsUpperUni (u₂ τ))
    (hu : ∀ τ, IsLowerUni (u τ)) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hap : ∀ τ, Antitone (ap τ)) (ham : ∀ τ, Antitone (am τ))
    (hcard : ∀ τ, ((Finset.range (p τ)).filter (fun i => ap τ i ≠ 0)).card +
      ((Finset.range (m - p τ)).filter (fun b => am τ b ≠ 0)).card ≤ n) :
    piAct p a e u₁ u₂ u (delta p (fun τ => m - p τ) ap am : MvPolynomial (FVar D m n) ℂ) =
      delta p (fun τ => m - p τ) ap am := by
  have hpoly : polySubst p u₁ u₂ u (delta p (fun τ => m - p τ) ap am : MvPolynomial (FVar D m n) ℂ) =
      delta p (fun τ => m - p τ) ap am := by
    unfold delta
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    unfold deltaAt
    rw [map_mul, map_prod, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [map_pow]
      by_cases h0 : ap τ i - (if i + 1 < p τ then ap τ (i + 1) else 0) = 0
      · rw [h0, pow_zero, pow_zero]
      · have hne : ap τ i ≠ 0 := by omega
        have := le_card_of_antitone (hap τ) hi hne
        have := hcard τ
        rw [polySubst_unip_minorPlus p hpm u₁ u₂ u hu₁ hu τ (i + 1) (by omega) (by omega)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [map_pow]
      by_cases h0 : am τ i - (if i + 1 < m - p τ then am τ (i + 1) else 0) = 0
      · rw [h0, pow_zero, pow_zero]
      · have hne : am τ i ≠ 0 := by omega
        have := le_card_of_antitone (ham τ) hi hne
        have := hcard τ
        rw [polySubst_unip_minorMinus p u₁ u₂ u hu₂ hu τ (i + 1) (by omega) (by have := hpm τ; omega)]
  have hchar : fockChar p a e u₁ u₂ u = 1 := by
    unfold fockChar
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [det_upperUni _ (hu₁ τ), det_upperUni _ (hu₂ τ), det_lowerUni _ (hu τ), _root_.one_zpow, _root_.one_zpow, _root_.one_zpow,
      mul_one, mul_one]
  unfold piAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, hpoly, hchar, one_smul]

end Extremal

theorem ioPiExists_of (h : IoPiFromHW D) : IoPiExists D := by
  intro θ V W S' M c BV p a e ap am hθ hV ha hW hBV hc hM hcw
  have hp : ∀ τ, p τ ≤ W.rank := fun τ => (hM τ).2.1
  have hap : ∀ τ, Antitone (ap τ) := fun τ => (hM τ).2.2.1
  have ham : ∀ τ, Antitone (am τ) := fun τ => (hM τ).2.2.2.1
  have hap0 : ∀ τ i, p τ ≤ i → ap τ i = 0 := fun τ => (hM τ).2.2.2.2.1
  have ham0 : ∀ τ b, W.rank - p τ ≤ b → am τ b = 0 := fun τ => (hM τ).2.2.2.2.2.1
  have hcard := fun τ => (hM τ).2.2.2.2.2.2.1
  exact h θ V W M c BV p a e ap am _ hθ hV ha hW hBV hc hM hcw (delta_ne_zero p ap am hp hap ham hcard)
    (fun t₁ t₂ t h1 h2 h3 => piAct_diag_delta p hp a e t₁ t₂ t h1 h2 h3 ap am hap ham hap0 ham0 hcard)
    (fun u₁ u₂ u hu₁ hu₂ hu => piAct_unip_delta p hp a e u₁ u₂ u hu₁ hu₂ hu ap am hap ham hcard)

section Assembly

variable {V W : HSp D} {S' : D.what₂.Tau → SPar}

theorem realKVLoc_of_at (M : DSModel W S') (p : D.what₂.Tau → ℕ) (nV : ℕ) (αV : D.what₂.Tau → ℚ)
    (ap am : D.what₂.Tau → ℕ → ℕ)
    (h : ∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) nV (αV τ) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ))) :
    RealKVLoc W M p nV αV := by
  intro τ
  obtain ⟨hε, h1, h2, h3, h4, h5, h6, h7⟩ := h τ
  exact ⟨hε, h1, ap τ, am τ, h2, h3, h4, h5, h6, h7⟩

theorem realKVCompatU_of (hFE : FockEquivOfReal D) (hIo : IoPiExists D) (hLine : LineAtExists D)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {αV αW : D.what₂.Tau → ℚ} (M : DSModel W S') (c : CoefA V)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (Δ : PolF D W.rank V.rank)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : ∀ τ, (gramAt D V τ).PosDef) (ha : 2 * a = (V.rank : ℤ))
    (hW : Odd W.rank) (hBV : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) (hc : c.Is)
    (hαV : ∀ τ, αV τ = -(e τ : ℚ)) (hαW : ∀ τ, αW τ = -(e τ : ℚ) - 1 / 2)
    (hM : ∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) V.rank (αV τ) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)))
    (hcw : CoefLowWt θ V BV c (nuDelta V.rank W.rank p e ap am))
    (hΔ : Δ = delta p (fun τ => W.rank - p τ) ap am) :
    RealKVCompatU ψ θ V W αV αW M c BV Δ := by
  subst hΔ
  have hM' : ∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) V.rank (-(e τ : ℚ)) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) := by
    intro τ; rw [← hαV τ]; exact hM τ
  have hp : ∀ τ, p τ ≤ W.rank := fun τ => (hM τ).2.1
  refine ⟨delta_ne_zero p ap am hp (fun τ => (hM τ).2.2.1) (fun τ => (hM τ).2.2.2.1)
    (fun τ => (hM τ).2.2.2.2.2.2.1), ?_⟩
  obtain ⟨io, h1, h2, h3⟩ := hIo θ V W M c BV p a e ap am hθ hV ha hW hBV hc hM' hcw
  refine ⟨io, fun χV χW hχV hχW ω hω f hf _ hvac => ⟨?_, ?_, h3⟩⟩
  · have hB : ∀ τ, IsUnit (BV τ).det := fun τ => Matrix.isUnit_det_of_left_inverse (hBV τ)
    have hT : ∀ τ, IsUnit (onb M τ).det := fun τ => by
      unfold onb; exact Matrix.isUnit_nonsing_inv_det_iff.mpr (isUnit_fr M τ)
    have hF := hFE hLine ψ θ V W χV χW ω (fun _ => 1) (cart M) BV (onb M) p a e hψ hω.real hθ hω.datum ha hp hW hV
      (fun τ => by rw [← hαV τ]; exact hχV τ) (fun τ => by rw [← hαW τ]; exact hχW τ)
      (fun τ => ⟨by rw [Matrix.mul_one], by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one],
        by rw [Matrix.mul_one]; exact hV τ⟩)
      (fun τ => cart_isCartanInv M τ) (fun τ => ⟨hBV τ, Matrix.one_mul _⟩) (fun τ => onb_props M p τ (hM τ).1)
    intro u hu x w
    rw [h1 u hu x w]
    have e1 : ∀ τ, blockDiagonalOfBlocks p (fun _ => 1) (fun _ => 1) τ = (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) := fun τ => by
      have := block_diagonal_of_blocks_eq p (fun _ => (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ))
        (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) τ
      rwa [extendOne_one p hp, symmetricScalarBlockMatrix_one_zero p] at this
    refine hF (fun _ => 1) (fun _ => 1) (hOf θ V BV u) (fun _ => one_mem _) (fun _ => one_mem _)
      (hOf_unitary hθ V hV BV hBV u) u 1 (isInfEl_hOf θ V BV hB u hu) ?_ f hf hvac (io x w)
    simp only [e1]
    exact isInfEl_one hθ W (onb M) hT
  · have hB : ∀ τ, IsUnit (BV τ).det := fun τ => Matrix.isUnit_det_of_left_inverse (hBV τ)
    have hT : ∀ τ, IsUnit (onb M τ).det := fun τ => by
      unfold onb; exact Matrix.isUnit_nonsing_inv_det_iff.mpr (isUnit_fr M τ)
    have hF := hFE hLine ψ θ V W χV χW ω (fun _ => 1) (cart M) BV (onb M) p a e hψ hω.real hθ hω.datum ha hp hW hV
      (fun τ => by rw [← hαV τ]; exact hχV τ) (fun τ => by rw [← hαW τ]; exact hχW τ)
      (fun τ => ⟨by rw [Matrix.mul_one], by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one],
        by rw [Matrix.mul_one]; exact hV τ⟩)
      (fun τ => cart_isCartanInv M τ) (fun τ => ⟨hBV τ, Matrix.one_mul _⟩) (fun τ => onb_props M p τ (hM τ).1)
    intro τ k hk v u hu w
    rw [h2 τ k hk v u hu w]
    have hkp := kAt_props p τ (M.ε τ) (hM τ).1 k hk
    refine hF (blk1 p (kAt τ k)) (blk2 p (kAt τ k)) (fun _ => 1)
      (first_diagonal_block_unitary p hp (kAt τ k) (fun τ' => (hkp τ').1) (fun τ' => (hkp τ').2))
      (second_diagonal_block_unitary p hp (kAt τ k) (fun τ' => (hkp τ').1) (fun τ' => (hkp τ').2))
      (fun _ => one_mem _) 1 (atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (isInfEl_one hθ V BV hB) ?_ f hf hvac _
    refine isInfEl_atTau hθ W τ _ (frk_unitary M τ k hk) _ ?_ ?_
    · rw [block_diagonal_of_blocks_eq p (kAt τ k) (fun τ' => (hkp τ').1) τ, kAt_self]
      unfold onb
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_fr M τ)]
    · intro τ' hne
      rw [block_diagonal_of_blocks_eq p (kAt τ k) (fun τ' => (hkp τ').1) τ', kAt_ne k hne, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hT τ')]

theorem realKVCompatU_of_hw (hFE : FockEquivOfReal D) (hHW : IoPiFromHW D) (hLine : LineAtExists D)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {αV αW : D.what₂.Tau → ℚ} (M : DSModel W S') (c : CoefA V)
    (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (Δ : PolF D W.rank V.rank)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : ∀ τ, (gramAt D V τ).PosDef) (ha : 2 * a = (V.rank : ℤ))
    (hW : Odd W.rank) (hBV : ∀ τ, (BV τ)ᴴ * gramAt D V τ * BV τ = 1) (hc : c.Is)
    (hαV : ∀ τ, αV τ = -(e τ : ℚ)) (hαW : ∀ τ, αW τ = -(e τ : ℚ) - 1 / 2)
    (hM : ∀ τ, (∀ i, M.ε τ i = decide ((i : ℕ) < p τ)) ∧
      KVWeightAt W.rank (p τ) V.rank (αV τ) (ap τ) (am τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)))
    (hcw : CoefLowWt θ V BV c (nuDelta V.rank W.rank p e ap am))
    (hΔ : Δ = delta p (fun τ => W.rank - p τ) ap am) :
    RealKVCompatU ψ θ V W αV αW M c BV Δ :=
  realKVCompatU_of hFE (ioPiExists_of hHW) hLine M c BV p a e ap am Δ hψ hθ hV ha hW hBV hc hαV hαW hM hcw hΔ

end Assembly

end Formalism.IndefR.Fock.IoExist

end
