import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.FrameChange

variable {D : D7}

theorem sign_eq_of_ne_zero {n : ℕ} {ε ε' : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * x = x * Formalism.REAL.Jm ε') {a i : Fin n} (hx : x a i ≠ 0) : ε a = ε' i := by
  have hc := congrFun (congrFun h a) i
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_contra hne
  apply hx
  cases h1 : ε a <;> cases h2 : ε' i <;> simp only [h1, h2] at hc hne
  · exact (hne trivial).elim
  · simp at hc; linear_combination -hc / 2
  · simp at hc; linear_combination hc / 2
  · exact (hne trivial).elim

theorem Jm_mul_fr {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) (h : Y.cart τ = X.cart τ) :
    Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) := by
  unfold Fr.cart at h
  calc Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹)
      = (X.fr τ * (X.fr τ)⁻¹) * Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) := by
        rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.one_mul]
    _ = X.fr τ * ((X.fr τ)⁻¹ * Formalism.REAL.Jm (X.ε τ) * X.fr τ) * (Y.fr τ)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X.fr τ * ((Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * Y.fr τ) * (Y.fr τ)⁻¹ := by rw [h]
    _ = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * (Y.fr τ * (Y.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.mul_one]

theorem fr_mul_inv_mul {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) :
    X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = 1 := by
  calc X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = X.fr τ * ((Y.fr τ)⁻¹ * Y.fr τ) * (X.fr τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.mul_one, GlobalTheory.CompactFockAction.fr_mul_inv]

section Coef

variable {V W : HSp D}

def coef (A A' : Fr V) (B B' : Fr W) (v : FVar D W.rank V.rank) (p : Fin W.rank × Fin V.rank) : ℂ :=
  if B'.ε v.1 v.2.1 = A'.ε v.1 v.2.2 then
    (B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2
  else starRingEnd ℂ ((B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2)

def sub (A A' : Fr V) (B B' : Fr W) : PolF D W.rank V.rank →ₐ[ℂ] PolF D W.rank V.rank :=
  MvPolynomial.aeval fun v => ∑ p, coef A A' B B' v p • (MvPolynomial.X (v.1, p.1, p.2) : PolF D W.rank V.rank)

end Coef

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem onb_eq (X Y : Fr V) (τ : D.what₂.Tau) : Y.onb τ = X.onb τ * (X.fr τ * (Y.fr τ)⁻¹) := by
  unfold Fr.onb
  rw [← Matrix.mul_assoc, GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.one_mul]

theorem inv_fr_mul (X Y : Fr V) (τ : D.what₂.Tau) : (X.fr τ * (Y.fr τ)⁻¹)⁻¹ = Y.fr τ * (X.fr τ)⁻¹ :=
  Matrix.inv_eq_left_inv (fr_mul_inv_mul Y X τ)

theorem aPlusAll_change (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) (v : FVar D W.rank V.rank)
    (g : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) :
    aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A'.onb B'.onb v g =
      ∑ p, coef A A' B B' v p •
        aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A.onb B.onb (v.1, p.1, p.2) g := by
  obtain ⟨ρ, i, j⟩ := v
  simp only [aPlusAll]
  rw [onb_eq A A' ρ, onb_eq B B' ρ, GlobalTheory.FockBasis.unitMap_mul, inv_fr_mul,
    GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.CompactFockAction.Jm_single A B ρ a b)]
  congr 1
  simp only [coef]
  by_cases hx : (B.fr ρ * (B'.fr ρ)⁻¹) a i * (A'.fr ρ * (A.fr ρ)⁻¹) j b = 0
  · simp [hx]
  · have h1 := sign_eq_of_ne_zero (Jm_mul_fr B B' ρ (hB ρ)) (left_ne_zero_of_mul hx)
    have h2 := sign_eq_of_ne_zero (Jm_mul_fr A' A ρ (hA ρ).symm) (right_ne_zero_of_mul hx)
    rw [h1, ← h2]
    simp only [decide_eq_true_eq]

theorem ptF_sub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (Q : PolF D W.rank V.rank) :
    ptF ψ θ A' B' f Q = ptF ψ θ A B f (sub A A' B B' Q) := by
  have e1 : A'.cart = A.cart := funext hA
  have e2 : B'.cart = B.cart := funext hB
  have hS := GlobalTheory.CompactFockAction.cart_isCartanInv A
  have hT := GlobalTheory.CompactFockAction.cart_isCartanInv B
  unfold ptF pureTensorO sub
  rw [e1, e2]
  have hAt : ∀ X Y i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ X Y i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (f + f') =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f +
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f' :=
    fun _ _ _ _ _ h h' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ X Y i (a : ℂ) f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (a • f) =
      a • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f :=
    fun _ _ _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ X Y i j f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j f) =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ i j _ h => GlobalTheory.FockSubst.aPlus_comm (sS := A.cart) (sT := B.cart) hψ hθ i.1 _ hS hT j.1 _ h
  exact GlobalTheory.FockSubst.pure_subst (P := IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (hAt _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hAt _ _) (Ac _ _)
    (Aadd _ _) (Asm _ _) (coef A A' B B') (fun v p => (v.1, p.1, p.2))
    (aPlusAll_change hψ hθ A A' B B' hA hB) hf Q

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D}

theorem coef_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ)
    (v : FVar D W.rank V.rank) (q : Fin W.rank × Fin V.rank) :
    ∑ p, coef X' X Y' Y v p * coef X X' Y Y' (v.1, p.1, p.2) q = if q = (v.2.1, v.2.2) then 1 else 0 := by
  obtain ⟨ρ, i, j⟩ := v

  have hK : ∀ c d, (∑ a, (Y'.fr ρ * (Y.fr ρ)⁻¹) a d * (Y.fr ρ * (Y'.fr ρ)⁻¹) c a) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul Y Y' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hU : ∀ c d, (∑ b, (X.fr ρ * (X'.fr ρ)⁻¹) c b * (X'.fr ρ * (X.fr ρ)⁻¹) b d) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul X X' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hprod : (∑ p : Fin W.rank × Fin V.rank, ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
      ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) = if q = (i, j) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (X.fr ρ * (X'.fr ρ)⁻¹) j b) *
        ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) =
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a) *
        ((X.fr ρ * (X'.fr ρ)⁻¹) j b * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) := fun a b => by ring
    simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, hU, hK]
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : q1 = i <;> by_cases h2 : j = q2 <;> (try simp [h1, h2]) <;> (try exact fun h => h1 h.symm) <;>
      (try exact fun h => h2 h.symm)

  have hterm : ∀ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q =
      if Y.ε ρ i = X.ε ρ j then
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)
      else starRingEnd ℂ (((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) := by
    intro p
    simp only [coef]
    by_cases hx : (Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2 = 0
    · simp [hx]
    · have h1 := sign_eq_of_ne_zero (Jm_mul_fr Y' Y ρ (hY ρ).symm) (left_ne_zero_of_mul hx)
      have h2 := sign_eq_of_ne_zero (Jm_mul_fr X X' ρ (hX ρ)) (right_ne_zero_of_mul hx)
      rw [h1, ← h2]
      split_ifs <;> simp [map_mul]
  by_cases hs : Y.ε ρ i = X.ε ρ j
  · simp only [hterm, hs, if_true]
    exact hprod
  · simp only [hterm, hs, if_false]
    rw [← map_sum, hprod]
    split_ifs <;> simp

theorem sub_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ) :
    (sub X X' Y Y').comp (sub X' X Y' Y) = AlgHom.id ℂ (PolF D W.rank V.rank) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  obtain ⟨ρ, i, j⟩ := v
  calc sub X X' Y Y' (sub X' X Y' Y (MvPolynomial.X (ρ, i, j)))
      = ∑ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p •
          ∑ q : Fin W.rank × Fin V.rank, coef X X' Y Y' (ρ, p.1, p.2) q •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [sub, MvPolynomial.aeval_X, map_sum, map_smul]
    _ = ∑ q : Fin W.rank × Fin V.rank, (∑ p : Fin W.rank × Fin V.rank,
          coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
    _ = ∑ q : Fin W.rank × Fin V.rank, (if q = (i, j) then (1 : ℂ) else 0) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [coef_comp X X' Y Y' hX hY (ρ, i, j)]
    _ = MvPolynomial.X (ρ, i, j) := by
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [hq]
        · simp

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

theorem ptF_frame_change : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  intro D ψ θ hψ hθ V W A A' B B' hA hB
  let e : PolF D W.rank V.rank ≃ₐ[ℂ] PolF D W.rank V.rank :=
    AlgEquiv.ofAlgHom (sub A' A B' B) (sub A A' B B') (sub_comp A' A B' B (fun τ => (hA τ).symm) fun τ => (hB τ).symm)
      (sub_comp A A' B B' hA hB)
  refine ⟨e.toLinearEquiv, fun f hf P => ?_⟩
  exact (ptF_sub hψ hθ A' A B' B (fun τ => (hA τ).symm) (fun τ => (hB τ).symm) hf P).symm

end GlobalTheory.FrameChange

end
