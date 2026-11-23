import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreApply

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.TorC

open CompanionTheory.D.LK (Pos)

section Abstract

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι]

def br (x y : R) : R := x * y - y * x

theorem br_mul (x y z : R) : br x (y * z) = br x y * z + y * br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_sub, sub_mul, mul_assoc]
  abel

theorem br_add_right (x y z : R) : br x (y + z) = br x y + br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_add_left (x y z : R) : br (x + y) z = br x z + br y z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_smul_right (r : ℂ) (x y : R) : br x (r • y) = r • br x y := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem br_sum_right {κ : Type*} (s : Finset κ) (x : R) (f : κ → R) : br x (∑ i ∈ s, f i) = ∑ i ∈ s, br x (f i) := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem br_anti (x y : R) : br x y = -br y x := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, neg_sub]

theorem swap3 {M : Type*} [AddCommMonoid M] (g : ι → ι → ι → M) :
    ∑ j, ∑ k, ∑ b, g j k b = ∑ b, ∑ k, ∑ j, g j k b := by
  calc ∑ j, ∑ k, ∑ b, g j k b = ∑ j, ∑ b, ∑ k, g j k b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, g j k b := Finset.sum_comm
    _ = ∑ b, ∑ k, ∑ j, g j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem swap4 {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b := by
  calc ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ i, ∑ j, ∑ b, ∑ k, f i j k b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ j, ∑ k, f i j k b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ j, ∑ k, f i j k b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ i, ∑ k, f i j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

def Dm (a c : ι → R) (A : ι → ι → ℂ) : R := ∑ i, ∑ k, A i k • (c k * a i)

theorem reindex (W : ι → ι → ι → R) (S : ι → ι → ι → ℂ) (A : ι → ι → ℂ) :
    ∑ i, ∑ j, ∑ k, S i j k • ((∑ l, A k l • W i j l) - (∑ b, A b j • W i b k) - ∑ b, A b i • W b j k) =
      ∑ i, ∑ j, ∑ k, ((∑ m, S i j m * A m k) - (∑ m, S i m k * A j m) - ∑ m, S m j k * A i m) • W i j k := by
  simp only [smul_sub, sub_smul, Finset.smul_sum, Finset.sum_smul, smul_smul, Finset.sum_sub_distrib]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  · exact Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.RealMult.TorC.swap3 _
  · exact GlobalTheory.CompanionTheory.RealMult.TorC.swap4 _

variable {a c : ι → R}

theorem term_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (a m) = -(if m = k then a i else 0) := by
  have h₁ : a i * a m = -(a m * a i) := eq_neg_of_add_eq_zero_left (haa i m)
  have h₂ : a m * c k = (if m = k then 1 else 0) - c k * a m := eq_sub_of_add_eq (hac m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (a m), h₂]
  split_ifs <;> simp only [sub_mul, mul_neg, mul_assoc, one_mul, zero_mul] <;> abel

theorem term_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (c m) = if i = m then c k else 0 := by
  have h₁ : a i * c m = (if i = m then 1 else 0) - c m * a i := eq_sub_of_add_eq (hac i m)
  have h₂ : c m * c k = -(c k * c m) := eq_neg_of_add_eq_zero_left (hcc m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (c m), h₂]
  split_ifs <;> simp only [mul_sub, neg_mul, mul_assoc, mul_one, mul_zero] <;> abel

theorem dm_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (a m) = -∑ i, A i m • a i := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (a m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (a m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • -(if m = k then a i else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_a haa hac]
    _ = -∑ i, A i m • a i := by
          simp [smul_ite, Finset.sum_neg_distrib]

theorem dm_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (c m) = ∑ k, A m k • c k := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (c m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (c m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • (if i = m then c k else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_c hcc hac]
    _ = ∑ k, A m k • c k := by
          rw [Finset.sum_comm]
          simp [smul_ite]

theorem bracket_wedge_formula (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (i j k : ι) :
    br (Dm a c A) (c k * a j * a i) =
      (∑ l, A k l • (c l * a j * a i)) - (∑ b, A b j • (c k * a b * a i)) - ∑ b, A b i • (c k * a j * a b) := by
  rw [GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_c hcc hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac]
  simp only [add_mul, mul_neg, neg_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, mul_assoc]
  abel

theorem br_lift_dm {L : R} (hLa : ∀ i, br L (a i) = 0) (hLc : ∀ i, br L (c i) = 0) (A : ι → ι → ℂ) :
    br L (Dm a c A) = 0 := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br_sum_right,
    GlobalTheory.CompanionTheory.RealMult.TorC.br_smul_right, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, hLa, hLc, zero_mul, mul_zero,
    add_zero, smul_zero, Finset.sum_const_zero]

end Abstract

section Car

variable {n : ℕ}

theorem key_lt (p : Pos n) : CompanionTheory.D.LK.key p < n * n := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨b, p⟩ := i
  obtain ⟨b', q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  cases b <;> cases b' <;> simp only [keyR, if_true, Bool.false_eq_true, if_false] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]

def tw (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem tw_self (i : Ix n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Ix n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Ix n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem liftR_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cr n V)
    (A : Finset (Ix n)) : liftR n T x A = T (x A) := rfl

theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftR n T : Module.End ℂ (Cr n V)) (liftR n S) = liftR n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftR_apply]

end Car

section Coefficients

variable {n : ℕ}

def bt (s a b : Bool) : ℂ :=
  if s then (if a then (if b then 1 else -1) else 0) else (if b then 0 else 1)

end Coefficients

section Units

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

end Units

end GlobalTheory.CompanionTheory.RealMult.TorC
