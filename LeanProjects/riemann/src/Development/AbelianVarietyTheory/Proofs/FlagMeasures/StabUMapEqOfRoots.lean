import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopAct

variable {n m : ℕ}

def IsMatOn (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ b, g *ᵥ f b = ∑ c, M c b • f c

theorem isMatOn_mul {g h : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g f M₁) (hh : IsMatOn h f M₂) : IsMatOn (g * h) f (M₁ * M₂) := by
  intro b
  rw [← Matrix.mulVec_mulVec, hh b, Matrix.mulVec_sum]
  have e : ∀ c, g *ᵥ (M₂ c b • f c) = ∑ d, (M₂ c b * M₁ d c) • f d := by
    intro c
    rw [Matrix.mulVec_smul, hg c, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem isMatOn_unique {g : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hf : LinearIndependent ℂ f) (hM : IsMatOn g f M₁) (hN : IsMatOn g f M₂) : M₁ = M₂ := by
  ext c b
  have h : ∑ d, (M₁ d b - M₂ d b) • f d = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hM b, ← hN b, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hf _ h c)

theorem isMatOn_conj {g P Pi : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g (fun j => P *ᵥ f j) A) (hP : Pi * P = 1) : IsMatOn (Pi * g * P) f A := by
  intro b
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg b, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

variable {N : ℕ}

theorem stabU_mul {Z a b : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z)
    (hb : b ∈ GlobalTheory.LoopV.stabU Z) : a * b ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul ha.1 hb.1, ?_⟩
  have e : Z * (a * b) * Z⁻¹ = (Z * a * Z⁻¹) * (Z * b * Z⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hZ]
  rw [e]
  exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul ha.2 hb.2

theorem stabU_inv {Z a : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z) :
    a⁻¹ ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨(Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1).1, ?_⟩
  have hai := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1
  have e : Z * a⁻¹ * Z⁻¹ = (Z * a * Z⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ, Matrix.mul_assoc]
  rw [e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv ha.2).1

theorem stabU_map_eq_ofRoots {K : Type} [Field K] (ψ : K →+* ℂ) (p : Point K N) (x : Matrix (Fin N) (Fin N) ℂ)
    (hx : x ∈ GlobalTheory.LoopV.stabU ((ptMat p).map ψ)) :
    x = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => x q.1.1 q.1.2) := by
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have hd' : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero ψ).2 (hd i)
  have hw' : ∀ i j, (ptMat p).map ψ i j = if j = σ i then ψ (d i) else 0 := by
    intro i j; rw [Matrix.map_apply, hw]; split_ifs <;> simp
  ext a b
  unfold GlobalTheory.LoopV.ofRoots
  by_cases hr : (a, b) ∈ GlobalTheory.LoopV.roots (ptMat p)
  · rw [dif_pos hr]
  · rw [dif_neg hr]
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [if_neg hab.ne]
      have hσ : σ.symm a < σ.symm b := by
        rw [GlobalTheory.LoopV.Cell.mono_roots hd hw] at hr
        push_neg at hr
        rcases (hr hab).lt_or_eq with h | h
        · exact h
        · exact absurd (σ.symm.injective h) hab.ne
      have h0 := (hx.2 (σ.symm a) (σ.symm b)).1 hσ
      rw [GlobalTheory.LoopV.Cell.mono_conj hd' hw'] at h0
      simp only [Equiv.apply_symm_apply, mul_eq_zero, inv_eq_zero, hd', false_or, or_false] at h0
      exact h0
    · rw [if_pos rfl]; exact (hx.1 a a).2 rfl
    · rw [if_neg hab.ne']; exact (hx.1 a b).1 hab

end GlobalTheory.LoopAct

end
