import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

open NumberField Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

open Formalism.MainNotions.S

def gLie {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Formalism.REAL.inG ε X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * a) + (bᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [Formalism.REAL.inG]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha, smul_zero]

def expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp (X : Matrix (Fin n) (Fin n) ℂ)).unit, Formalism.REAL.f1alg_exp_inUJ ε X.1 X.2⟩

@[simp] theorem uMat_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) :
    uMat (expU X) = NormedSpace.exp (X : Matrix (Fin n) (Fin n) ℂ) := rfl

def IsONBasis {n m : ℕ} {ε : Fin n → Bool} (E : Fin m → gLie ε) : Prop :=
  (∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
      if i = j then 1 else 0) ∧
    Submodule.span ℝ (Set.range E) = ⊤

variable (B : RowsAut)

abbrev gInf : Type := ∀ v : InfinitePlace B.I.F, gLie (B.I.ε v)

open Classical in

def atPlace (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) : gInf B := Pi.single v X

def orbit (E : gInf B) (w : B.Hs) (t : ℝ) : B.Hs := B.σs (fun v => expU (t • E v)) w

def dAct (E : gInf B) (w : B.Hs) : B.Hs := deriv (orbit B E w) 0

def wordAct (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (w : B.Hs) : B.Hs :=
  l.foldr (fun X y => dAct B (atPlace B X.1 X.2) y) w

def VP (P : ℕ) : Submodule ℂ B.Hs :=
  Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (u : ∀ v, B.H v),
    l.length ≤ P ∧ (∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧ y = wordAct B l (B.tens u)}

def beP (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def StepBoundAt (b : ℝ) (P : ℕ) : Prop :=
  FiniteDimensional ℂ (VP B P) ∧
  (∀ k : B.I.Ginf, (∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) → ∀ w ∈ VP B P, B.σs k w ∈ VP B P) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P, DifferentiableAt ℝ (orbit B E w) 0) ∧
  (∀ (v : InfinitePlace B.I.F) (m : ℕ) (E : Fin m → gLie (B.I.ε v)), IsONBasis E → ∀ w ∈ VP B P,
    ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ beP B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧
  (∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
    ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P,
    ‖dAct B E w‖ ≤ Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖) ∧
  ∀ (E : gInf B), ∀ w ∈ VP B P, dAct B E w ∈ VP B (P + 1)

def StepBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (b : ℝ), GlobalTheory.Count.IsDSData B d →
    (∀ v a, |B.lam v a| ≤ b ^ 2) → ∀ P : ℕ, StepBoundAt B b P

open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.stepSpan_mono {P Q : ℕ} (h : P ≤ Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ≤ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B Q :=
  Submodule.span_mono fun _ ⟨l, u, hl, hu, hy⟩ => ⟨l, u, hl.trans h, hu, hy⟩

open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem {d : InfinitePlace B.I.F → ℝ}
    (h : _root_.GlobalTheory.Count.IsDSData B d) (P : ℕ) :
    B.tens B.w ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ∧ ‖B.tens B.w‖ = 1 := by
  have hd := h
  unfold _root_.GlobalTheory.Count.IsDSData at hd
  have hunit : ∀ v, ‖B.w v‖ = 1 ∧ B.w v ∈ _root_.Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) := fun v => by
    have hv := (hd v).2.2.1
    unfold _root_.Formalism.MainNotions.S.IsLowUnit at hv
    exact hv
  refine ⟨Submodule.subset_span ⟨[], B.w, Nat.zero_le _, fun v => (hunit v).2, rfl⟩, ?_⟩
  have hs := B.tens_spec
  unfold _root_.Formalism.MainNotions.S.AutInst.IsHilbTensor at hs
  have hinner : inner ℂ (B.tens B.w) (B.tens B.w) = 1 := by
    rw [hs.1]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (hunit v).1]
    simp
  have hsq : ‖B.tens B.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner, RCLike.one_re]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

example (ε : Fin 1 → Bool) : ∃ E : Fin 1 → gLie ε, IsONBasis E := by
  have hm : ∀ t : ℝ, Formalism.REAL.inG ε (!![(t : ℂ) * Complex.I]) := by
    intro t
    ext i j
    fin_cases i; fin_cases j
    by_cases h : ε 0 = true <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, h]
  refine ⟨fun _ => ⟨!![((1 : ℝ) : ℂ) * Complex.I], hm 1⟩, ?_, ?_⟩
  · intro i j
    fin_cases i; fin_cases j
    simp [Matrix.trace, Matrix.vecMul, dotProduct]
  · rw [eq_top_iff]
    rintro ⟨X, hX⟩ -
    have h0 : (X 0 0).re = 0 := by
      have := congrArg Complex.re (congrFun (congrFun hX 0) 0)
      by_cases h : ε 0 = true <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, h] at this <;> linarith
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun _ => (X 0 0).im, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp [Complex.ext_iff, h0]

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
