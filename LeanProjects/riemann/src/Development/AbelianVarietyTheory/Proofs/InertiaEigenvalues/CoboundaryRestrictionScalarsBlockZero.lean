import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon
open Matrix

theorem blockDiagonal_map_mulVec {R S : Type*} [CommSemiring R] [CommSemiring S] {n : Type} [Fintype n]
    [DecidableEq n] {r : ℕ} (D : Fin r → Matrix n n R) (f : R →+* S) (w : n × Fin r → S) (i : n) (k : Fin r) :
    ((blockDiagonal D).map f *ᵥ w) (i, k) = ((D k).map f *ᵥ fun j => w (j, k)) i := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, map_apply, blockDiagonal_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [apply_ite f]

theorem ks_algebraMap_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    algebraMap ℚ_[l] (Bst P) q = ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) := by
  simp only [ks, RingHom.comp_apply]
  rw [Polynomial.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem coboundary_block_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ), 0 < r →
    ∀ (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]) (β : n × Fin r → Bst P),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (β x)) - β) →
    ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) =
      ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P n _ _ K r hr σ ρ₀ p c c₀ β hK hconj hpc hβ
  set M : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
  refine ⟨fun i => (M.map (ks P) *ᵥ β) (i, ⟨0, hr⟩), fun g => ?_⟩
  have hD : M.map (ks P) *ᵥ (fun x => actSt P (g : GQ l) (β x)) =
      fun x => actSt P (g : GQ l) ((M.map (ks P) *ᵥ β) x) := by
    funext x
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_ks P g (hK x j)]
  have hC : M.map (ks P) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) =
      (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).map (ks P) * M.map (ks P) := by
    have e : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) =
        ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (ks P) := by
      rw [Matrix.map_map]; congr 1; funext q; exact ks_algebraMap_q P q
    rw [e, ← Matrix.map_mul, hconj g, Matrix.map_mul]
  have h1 : (fun x : n × Fin r => ks P (fr l x.2 (c g x.1))) =
      M.map (ks P) *ᵥ (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) := by
    funext x
    have e : (ks P) ∘ (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) = fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x) := by
      funext y; exact (ks_algebraMap_q P _).symm
    rw [← congrFun (hpc g) x, RingHom.map_mulVec, e]
  have hv : (fun x : n × Fin r => ks P (fr l x.2 (c g x.1))) =
      (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).map (ks P) *ᵥ
        (fun x => actSt P (g : GQ l) ((M.map (ks P) *ᵥ β) x)) - M.map (ks P) *ᵥ β := by
    rw [h1, hβ g, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hC, ← Matrix.mulVec_mulVec, hD]
  funext i
  have h := congrFun hv (i, ⟨0, hr⟩)
  rw [Pi.sub_apply, blockDiagonal_map_mulVec] at h
  exact h

end GlobalTheory.PMon

end
