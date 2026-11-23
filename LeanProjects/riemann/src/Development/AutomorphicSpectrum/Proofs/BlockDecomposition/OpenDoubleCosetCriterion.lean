import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.OpenOrbit

section Perm

variable {k : Type} [Field k]

def permGL {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k where
  val := (1 : Matrix _ _ k).submatrix σ id
  inv := (1 : Matrix _ _ k).submatrix id σ
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv σ
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ σ _ σ.bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

theorem permGL_mul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (B : Matrix (Fin N) (Fin N) k) (a c : Fin N) :
    (((permGL σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) * B) a c = B (σ a) c := by
  show (((1 : Matrix (Fin N) (Fin N) k).submatrix σ id) * B) a c = _
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem vecMul_single_one {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (a : Fin N) :
    vecMul (Pi.single a 1) M = M a := by
  ext c
  simp [vecMul, dotProduct, Pi.single_apply]

end Perm

section Orbit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inr_ne_inl {r t N : ℕ} (h : r + t = N) (j : Fin t) (l : Fin r) :
    stdSum h (Sum.inr j) ≠ stdSum h (Sum.inl l) := fun e => by
  simpa using (stdSum h).injective e

theorem wPerm_first {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e]
  exact ePG_false_last i t

theorem lastRow_wInv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) 1 := by
  rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  ext c
  show (1 : Matrix _ _ k).submatrix id (wPerm h) (Fin.last (i + t)) c = _
  rw [← wPerm_first h]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lastRow_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hp : p ∈ Mir k (i + t)) :
    vecMul (eLast k (i + t)) (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (stdSum h (Sum.inl (Fin.last i))) := by
  have hp' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t) :=
    (Mir k (i + t)).inv_mem hp
  rw [show (q * wGL k h * p)⁻¹ = p⁻¹ * (wGL k h)⁻¹ * q⁻¹ by simp [mul_assoc], Units.val_mul, Units.val_mul,
    ← vecMul_vecMul, ← vecMul_vecMul, hp', lastRow_wInv, vecMul_single_one]

theorem exists_ne_of_mem {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hq : q ∈ parab k (two (stdSum h))) (hp : p ∈ Mir k (i + t)) :
    ∃ a : Fin (i + 1), (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  let r : parab k (two (stdSum h)) := ⟨q⁻¹, inv_mem hq⟩
  let M : GL (Fin (i + 1)) k := leviProj k (two (stdSum h)) r false
  have hrow : ∀ a, (M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) (Fin.last i) a = 0 := fun a => by
    have e := congrFun (lastRow_inv h q p hp) (stdSum h (Sum.inl a))
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one, hc a] at e
    exact e.symm
  have h1 : ((M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) *
      ((M⁻¹ : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)) (Fin.last i) (Fin.last i) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  rw [Matrix.mul_apply] at h1
  simp [hrow] at h1

theorem exists_parab_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Fin (i + t + 1) → k) (a : Fin (i + 1))
    (ha : y (stdSum h (Sum.inl a)) ≠ 0) :
    ∃ b ∈ parab k (two (stdSum h)),
      (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (stdSum h (Sum.inl (Fin.last i))) = y := by
  obtain ⟨b, -, -, hb⟩ := exists_rowSec (k := k) (stdSum h (Sum.inl a))
  have hb0 := hb y ha
  have hbQ : b y ∈ parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · rw [hb0, two_true, two_false, Matrix.updateRow_ne (stdSum_inr_ne_inl h l a),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  have hmQ : (permGL (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i)))) : GL (Fin (i + t + 1)) k) ∈
      parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i))) (stdSum h (Sum.inr l)))
        (stdSum h (Sum.inl j)) = 0
      rw [Equiv.swap_apply_of_ne_of_ne (stdSum_inr_ne_inl h l a) (stdSum_inr_ne_inl h l _),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  refine ⟨_, mul_mem hmQ hbQ, ?_⟩
  funext c
  rw [Units.val_mul, permGL_mul_apply, Equiv.swap_apply_right, hb0, Matrix.updateRow_self]

theorem mem_of_ne {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a : Fin (i + 1))
    (ha : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  obtain ⟨b, hbQ, hrow⟩ := exists_parab_row h _ a ha
  refine ⟨b⁻¹, inv_mem hbQ, (wGL k h)⁻¹ * b * g, ?_, by group⟩
  show vecMul (eLast k (i + t)) (((wGL k h)⁻¹ * b * g : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t)
  have e : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      vecMul (eLast k (i + t)) ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) := by
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, lastRow_wInv, vecMul_single_one, hrow, e,
    vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]

end Orbit

end GlobalTheory.CompanionTheory.BZRes.OpenOrbit

namespace GlobalTheory.CompanionTheory.BZRes

theorem mem_dcos_wGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔
      ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  intro k _ _ _ _ i t h _ g
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact OpenOrbit.exists_ne_of_mem h q p hq hp
  · rintro ⟨a, ha⟩
    exact OpenOrbit.mem_of_ne h g a ha

end GlobalTheory.CompanionTheory.BZRes

end
