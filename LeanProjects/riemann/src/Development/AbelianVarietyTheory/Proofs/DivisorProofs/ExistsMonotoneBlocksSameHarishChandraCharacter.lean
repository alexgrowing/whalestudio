import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCSort

open Formalism.L2.PT GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem trace_conj_rep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (P g : G) : LinearMap.trace ℂ V (ρ (P * g * P⁻¹)) = LinearMap.trace ℂ V (ρ g) := by
  let E : V ≃ₗ[ℂ] V := LinearEquiv.ofLinear (ρ P) (ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (ρ P * ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (ρ P⁻¹ * ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)
  have h : E.conj (ρ g) = ρ (P * g * P⁻¹) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply, map_mul, map_mul]
    rfl
  rw [← h, LinearMap.trace_conj']

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {s : ℕ}

def blockEquiv (e : ι ≃ κ) (b : ι → Fin s) (c : Fin s) : {i // b i = c} ≃ {k // (b ∘ e.symm) k = c} :=
  e.subtypeEquiv (fun i => by simp)

def lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s) :
    FDRep ℂ (GL {k // (b ∘ e.symm) k = c} K) :=
  transp (blockEquiv e b c) (lam c)

theorem mem_parab_symm (e : ι ≃ κ) (b : ι → Fin s) (p : parab K (b ∘ e.symm)) :
    (glEquiv K e).symm p.1 ∈ parab K b := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e.symm e.symm (p.1 : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL κ K) : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h2 _ _ (by simpa using hij)

theorem mem_parab (e : ι ≃ κ) (b : ι → Fin s) (p : parab K b) :
    glEquiv K e p.1 ∈ parab K (b ∘ e.symm) := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e e (p.1 : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e e ((p.1⁻¹ : GL ι K) : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h2 _ _ (by simpa using hij)

theorem infl_symm (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (p : parab K (b ∘ e.symm)) :
    infl K b lam ⟨(glEquiv K e).symm p.1, mem_parab_symm e b p⟩ = infl K (b ∘ e.symm) (lamT e b lam) p := by
  unfold infl
  congr 1

def hcEquiv (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    hcSpace K b lam ≃ₗ[ℂ] hcSpace K (b ∘ e.symm) (lamT e b lam) where
  toFun F := ⟨fun x => F.1 ((glEquiv K e).symm x), fun p x => by
    show F.1 ((glEquiv K e).symm (p.1 * x)) = infl K (b ∘ e.symm) (lamT e b lam) p (F.1 ((glEquiv K e).symm x))
    rw [map_mul, ← infl_symm]
    exact F.2 ⟨_, mem_parab_symm e b p⟩ _⟩
  map_add' F G := rfl
  map_smul' a F := rfl
  invFun F := ⟨fun y => F.1 (glEquiv K e y), fun p y => by
    show F.1 (glEquiv K e (p.1 * y)) = infl K b lam p (F.1 (glEquiv K e y))
    have hp : (⟨(glEquiv K e).symm (glEquiv K e p.1), mem_parab_symm e b ⟨_, mem_parab e b p⟩⟩ : parab K b) = p :=
      Subtype.ext ((glEquiv K e).symm_apply_apply p.1)
    have hi : infl K b lam p = infl K b lam ⟨(glEquiv K e).symm (glEquiv K e p.1), _⟩ := congrArg _ hp.symm
    rw [map_mul, hi]
    exact (F.2 ⟨_, mem_parab e b p⟩ (glEquiv K e y)).trans
      (LinearMap.congr_fun (infl_symm e b lam ⟨_, mem_parab e b p⟩).symm _)⟩
  left_inv F := by
    apply Subtype.ext
    funext y
    show F.1 ((glEquiv K e).symm (glEquiv K e y)) = F.1 y
    rw [MulEquiv.symm_apply_apply]
  right_inv F := by
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x)) = F.1 x
    rw [MulEquiv.apply_symm_apply]

theorem trace_hcRep_lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (g : GL κ K) :
    LinearMap.trace ℂ _ (hcRep K (b ∘ e.symm) (lamT e b lam) g) =
      LinearMap.trace ℂ _ (hcRep K b lam ((glEquiv K e).symm g)) := by
  have hconj : (hcEquiv e b lam).conj (hcRep K b lam ((glEquiv K e).symm g)) = hcRep K (b ∘ e.symm) (lamT e b lam) g := by
    apply LinearMap.ext
    intro F
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x * (glEquiv K e).symm g)) = F.1 (x * g)
    rw [← map_mul, MulEquiv.apply_symm_apply]
  rw [← hconj, LinearMap.trace_conj']

end GlobalTheory.HCSort

namespace GlobalTheory.HCSort

theorem exists_monotone_same_trace : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  intro K _ _ _ r s b lam hb hl
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  refine ⟨b ∘ e.symm, lamT e b lam, hb.comp e.symm.surjective,
    fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1, Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, ?_, fun x => ?_⟩
  · show Monotone (b ∘ (Tuple.sort b).symm.symm)
    rw [Equiv.symm_symm]
    exact Tuple.monotone_sort b
  · rw [trace_hcRep_lamT]
    have h : (glEquiv K e).symm x = glEquiv K e.symm x := by
      apply Units.ext
      rfl
    rw [h, GlobalTheory.SerOSys.TranspLabel.glEquiv_perm, trace_conj_rep]

end GlobalTheory.HCSort
