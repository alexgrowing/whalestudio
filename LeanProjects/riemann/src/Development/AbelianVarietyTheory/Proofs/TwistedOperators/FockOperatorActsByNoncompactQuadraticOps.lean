import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkewStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockLieQuad

open Complex MvPolynomial
open scoped ComplexConjugate

section Comb

variable {W : Type} [AddCommGroup W] [Module ℂ W] (φ : ℂ →+* ℂ)

theorem half_sum {k : ℕ} (A : Fin k → Prop) [DecidablePred A] (Y : Fin k → Fin k → ℂ)
    (h0 : ∀ i j, (A i ↔ A j) → Y i j = 0) (hc : ∀ i j, conj (Y i j) = Y j i) (V : Fin k → W) (i₀ : Fin k) :
    (∑ i, ∑ i', if A i ∧ ¬ A i' then
      φ (Y i i') • ((if i₀ = i then V i' else 0) + (if i₀ = i' then V i else 0)) else 0) =
    ∑ i, φ (if A i then Y i i₀ else conj (Y i i₀)) • V i := by
  have e : ∀ i i', (if A i ∧ ¬ A i' then
      φ (Y i i') • ((if i₀ = i then V i' else 0) + (if i₀ = i' then V i else 0)) else 0) =
      (if i₀ = i then (if A i ∧ ¬ A i' then φ (Y i i') • V i' else 0) else 0) +
      (if i₀ = i' then (if A i ∧ ¬ A i' then φ (Y i i') • V i else 0) else 0) := fun i i' => by
    split_ifs <;> simp
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : A i <;> by_cases h2 : A i₀
  · simp [h1, h2, h0 i i₀ (by simp [h1, h2])]
  · simp [h1, h2]
  · simp [h1, h2, hc]
  · simp [h1, h2, h0 i i₀ (by simp [h1, h2])]

variable {m n pS pT : ℕ} {YS : Matrix (Fin n) (Fin n) ℂ} {YT : Matrix (Fin m) (Fin m) ℂ}

def lin (pS pT : ℕ) (N : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (d : Fin n) : ℂ :=
  if (i.val < pT ↔ d.val < pS) then N i d else conj (N i d)

def act (YS : Matrix (Fin n) (Fin n) ℂ) (YT : Matrix (Fin m) (Fin m) ℂ) (N : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ := YT * N - N * YS

theorem comb (hS : IsPMat pS YS) (hT : IsPMat pT YT) (V : Fin m → Fin n → W) (i₀ : Fin m) (c₀ : Fin n) :
    (∑ c : Fin n, ∑ i : Fin m, ∑ i' : Fin m, if (i.val < pT ↔ c.val < pS) ∧ ¬ (i'.val < pT ↔ c.val < pS) then
      φ (YT i i') • ((if (i₀, c₀) = (i, c) then V i' c else 0) + (if (i₀, c₀) = (i', c) then V i c else 0)) else 0) +
    (∑ i : Fin m, ∑ d : Fin n, ∑ c : Fin n, if (i.val < pT ↔ d.val < pS) ∧ ¬ (i.val < pT ↔ c.val < pS) then
      φ (-(YS c d)) • ((if (i₀, c₀) = (i, d) then V i c else 0) + (if (i₀, c₀) = (i, c) then V i d else 0)) else 0) =
    ∑ i, ∑ d, φ (lin pS pT (act YS YT (single i₀ c₀ 1)) i d) • V i d := by
  have e : ∀ i d, φ (lin pS pT (act YS YT (single i₀ c₀ 1)) i d) • V i d =
      (if c₀ = d then φ (if (i.val < pT ↔ d.val < pS) then YT i i₀ else conj (YT i i₀)) • V i d else 0) +
      (if i₀ = i then φ (if (i.val < pT ↔ d.val < pS) then -YS c₀ d else conj (-YS c₀ d)) • V i d else 0) := by
    intro i d
    have e1 : act YS YT (single i₀ c₀ 1) i d = (if c₀ = d then YT i i₀ else 0) + (if i₀ = i then -YS c₀ d else 0) := by
      simp only [act, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
      by_cases h1 : c₀ = d <;> by_cases h2 : i₀ = i <;> simp [h1, h2, sub_eq_add_neg]
    rw [lin, e1]
    split_ifs <;> simp [sub_eq_add_neg, add_smul]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  · rw [Finset.sum_eq_single c₀ (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
    simp only [Prod.mk.injEq, and_true]
    exact half_sum φ (fun i : Fin m => i.val < pT ↔ c₀.val < pS) YT (fun i j h => hT.2 i j (by tauto))
      (fun i j => congrFun (congrFun hT.1 j) i) (fun i => V i c₀) i₀
  · rw [Finset.sum_eq_single i₀ (fun c _ hc => by simp [Ne.symm hc]) (by simp), Finset.sum_comm (s := Finset.univ)
      (t := Finset.univ) (f := fun (i : Fin m) (d : Fin n) => if i₀ = i then _ else _)]
    simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact half_sum φ (fun d : Fin n => i₀.val < pT ↔ d.val < pS) (fun d c => -YS c d)
      (fun i j h => by rw [hS.2 j i (by tauto), neg_zero])
      (fun i j => by rw [map_neg]; exact congrArg _ (congrFun (congrFun hS.1 i) j)) (fun i => V i₀ i) c₀

end Comb

section Poly

theorem quadOp_X_mul {ι : Type} [DecidableEq ι] (c : ℂ) (z z' y : ι) (P : MvPolynomial ι ℂ) :
    quadOp c z z' (X y * P) = X y * quadOp c z z' P -
      conj c • ((if y = z then pderiv z' P else 0) + (if y = z' then pderiv z P else 0)) := by
  have hd : ∀ (i : ι) (Q : MvPolynomial ι ℂ), pderiv i (X y * Q) = X y * pderiv i Q + (if y = i then Q else 0) :=
    fun i Q => by
      rw [pderiv_mul, pderiv_X, add_comm, Pi.single_apply]
      split_ifs <;> simp
  unfold quadOp
  rw [hd, map_add, hd, apply_ite (pderiv z), map_zero, mul_sub, mul_smul_comm, mul_smul_comm, mul_left_comm _ (X y),
    add_assoc, smul_add, sub_sub]

theorem pderiv_quadOp_one {ι : Type} [DecidableEq ι] (c : ℂ) (z z' y : ι) :
    pderiv y (quadOp c z z' (1 : MvPolynomial ι ℂ)) =
      c • ((if y = z then X z' else 0) + (if y = z' then X z else 0)) := by
  unfold quadOp
  simp only [pderiv_mul, pderiv_X, Pi.single_apply, map_add, mul_one, pderiv_one, map_zero, smul_zero, sub_zero, Derivation.map_smul]
  simp only [@eq_comm _ y, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]

variable {D : D7} {m n pS pT : ℕ} {YS : Matrix (Fin n) (Fin n) ℂ} {YT : Matrix (Fin m) (Fin m) ℂ} {τ : D.what₂.Tau}

theorem fockOperator_add (P Q : MvPolynomial (FVar D m n) ℂ) :
    fockP τ pS pT YS YT (P + Q) = fockP τ pS pT YS YT P + fockP τ pS pT YS YT Q := by
  have e : ∀ (p : Prop) [Decidable p] c (z z' : FVar D m n), (if p then quadOp c z z' (P + Q) else 0) =
      (if p then quadOp c z z' P else 0) + (if p then quadOp c z z' Q else 0) := fun p _ c z z' => by
    unfold quadOp
    split_ifs
    · simp only [map_add, mul_add, smul_add]; abel
    · simp
  simp only [fockP, e, Finset.sum_add_distrib]
  abel

theorem fockP_C (a : ℂ) : fockP τ pS pT YS YT (C a) = a • fockP τ pS pT YS YT 1 := by
  have e : ∀ (p : Prop) [Decidable p] c (z z' : FVar D m n), (if p then quadOp c z z' (C a) else 0) =
      a • (if p then quadOp c z z' 1 else 0) := fun p _ c z z' => by
    unfold quadOp
    split_ifs
    · simp [smul_comm a c, mul_comm _ (C a), C_mul']
    · simp
  simp only [fockP, e, Finset.smul_sum, smul_add]

open Classical in
theorem fockP_X_mul (hS : IsPMat pS YS) (hT : IsPMat pT YT) (y : FVar D m n) (P : MvPolynomial (FVar D m n) ℂ) :
    fockP τ pS pT YS YT (X y * P) = X y * fockP τ pS pT YS YT P - if y.1 = τ then
      ∑ i, ∑ d, conj (lin pS pT (act YS YT (single y.2.1 y.2.2 1)) i d) • pderiv (τ, i, d) P else 0 := by
  have e : ∀ (p : Prop) [Decidable p] c (z z' : FVar D m n), (if p then quadOp c z z' (X y * P) else 0) =
      X y * (if p then quadOp c z z' P else 0) - (if p then
        conj c • ((if y = z then pderiv z' P else 0) + (if y = z' then pderiv z P else 0)) else 0) :=
    fun p _ c z z' => by
      by_cases h : p
      · rw [if_pos h, if_pos h, if_pos h, quadOp_X_mul]
      · rw [if_neg h, if_neg h, if_neg h, mul_zero, sub_zero]
  unfold fockP
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sub_add_sub_comm, mul_add]
  refine congrArg₂ (· - ·) rfl ?_
  obtain ⟨ρ, i₀, c₀⟩ := y
  dsimp only
  split_ifs with h
  · subst h
    rw [← comb (starRingEnd ℂ) hS hT (fun i d => pderiv (ρ, i, d) P) i₀ c₀]
    simp only [Prod.mk.injEq, true_and]
  · simp [h]

open Classical in
theorem pderiv_fockP_one (hS : IsPMat pS YS) (hT : IsPMat pT YT) (y : FVar D m n) :
    pderiv y (fockP τ pS pT YS YT 1) = if y.1 = τ then
      ∑ i, ∑ d, lin pS pT (act YS YT (single y.2.1 y.2.2 1)) i d • X (τ, i, d) else 0 := by
  obtain ⟨ρ, i₀, c₀⟩ := y
  simp only [fockP, map_add, map_sum, apply_ite (pderiv _), map_zero, pderiv_quadOp_one]
  split_ifs with h
  · subst h
    have := comb (RingHom.id ℂ) hS hT (fun i d => (X (ρ, i, d) : MvPolynomial (FVar D m n) ℂ)) i₀ c₀
    simp only [Prod.mk.injEq, true_and, RingHom.id_apply] at this ⊢
    exact this
  · simp [h]

theorem fockOperator_one_mem (K : Submodule ℂ (MvPolynomial (FVar D m n) ℂ)) (h : ∀ y P, X y * P ∈ K) :
    fockP τ pS pT YS YT 1 ∈ K := by
  have e : ∀ (p : Prop) [Decidable p] c (z z' : FVar D m n), (if p then quadOp c z z' 1 else 0) ∈ K :=
    fun p _ c z z' => by
      split_ifs
      · simp only [quadOp, pderiv_one, map_zero, smul_zero, sub_zero, mul_one]
        exact K.smul_mem _ (h _ _)
      · exact K.zero_mem
  exact K.add_mem (K.sum_mem fun _ _ => K.sum_mem fun _ _ => K.sum_mem fun _ _ => e _ _ _ _)
    (K.sum_mem fun _ _ => K.sum_mem fun _ _ => K.sum_mem fun _ _ => e _ _ _ _)

end Poly

section Ops

variable {M : Type} [AddCommGroup M] [Module ℂ M] {m n : ℕ}

def sg {k : ℕ} (p : ℕ) (i : Fin k) : ℂ := if i.val < p then 1 else -1

def cplx (pS pT : ℕ) (N : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  cplxO (diagonal (sg pS)) (diagonal (sg pT)) N

def cre (pS pT : ℕ) (d : Matrix (Fin m) (Fin n) ℂ →+ Module.End ℂ M) (N : Matrix (Fin m) (Fin n) ℂ) :
    Module.End ℂ M := d N - I • d (cplx pS pT N)

def ann (pS pT : ℕ) (d : Matrix (Fin m) (Fin n) ℂ →+ Module.End ℂ M) (N : Matrix (Fin m) (Fin n) ℂ) :
    Module.End ℂ M := d N + I • d (cplx pS pT N)

variable {pS pT : ℕ} {YS : Matrix (Fin n) (Fin n) ℂ} {YT : Matrix (Fin m) (Fin m) ℂ}

theorem cplx_single (i : Fin m) (j : Fin n) (w : ℂ) :
    cplx pS pT (single i j w) = (w * I * if (i.val < pT ↔ j.val < pS) then 1 else -1) • single i j (1 : ℂ) := by
  ext a b
  simp only [cplx, cplxO, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    by_cases h1 : i.val < pT <;> by_cases h2 : j.val < pS <;> simp [sg, h1, h2, mul_comm]
  · simp [h]

theorem anti_diag {k p : ℕ} {Y : Matrix (Fin k) (Fin k) ℂ} (h : IsPMat p Y) :
    Y * diagonal (sg p) = -(diagonal (sg p) * Y) := by
  ext a b
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h1 : a.val < p <;> by_cases h2 : b.val < p <;> simp [sg, h1, h2, h.2 a b]

theorem act_cplx (hS : IsPMat pS YS) (hT : IsPMat pT YT) (N : Matrix (Fin m) (Fin n) ℂ) :
    act YS YT (cplx pS pT N) = -cplx pS pT (act YS YT N) := by
  have h1 := anti_diag hT
  have h2 := neg_eq_iff_eq_neg.2 (anti_diag hS)
  unfold act cplx cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc _ _ YS, ← h2]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, smul_sub, smul_neg]
  abel

theorem expand {d : Matrix (Fin m) (Fin n) ℂ →+ Module.End ℂ M} (hd : ∀ (t : ℝ) z, d ((t : ℂ) • z) = (t : ℂ) • d z)
    (N : Matrix (Fin m) (Fin n) ℂ) :
    cre pS pT d N = ∑ i, ∑ j, lin pS pT N i j • cre pS pT d (single i j 1) ∧
    ann pS pT d N = ∑ i, ∑ j, conj (lin pS pT N i j) • ann pS pT d (single i j 1) := by
  have hs : ∀ (w : ℂ) u, d (w • u) = (w.re : ℂ) • d u + (w.im : ℂ) • d (I • u) := fun w u => by
    rw [← hd, ← hd, ← map_add, smul_smul, ← add_smul, Complex.re_add_im]
  have e : N = ∑ i, ∑ j, single i j (N i j) := Matrix.matrix_eq_sum_single N
  have e1 : d N = ∑ i, ∑ j, d (single i j (N i j)) := by
    conv_lhs => rw [e]
    simp only [map_sum]
  have e2 : d (cplx pS pT N) = ∑ i, ∑ j, d (cplx pS pT (single i j (N i j))) := by
    conv_lhs => rw [e]
    simp only [cplx, cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, map_sum]
  have e3 : ∀ i j, single i j (N i j) = N i j • single i j (1 : ℂ) := fun i j => by simp
  unfold cre ann
  rw [e1, e2]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  constructor <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_ <;>
  · rw [cplx_single, cplx_single, e3, lin, hs (N i j), hs (N i j * _ * _), hs (1 * _ * _)]
    obtain ⟨x, y, h⟩ : ∃ x y : ℝ, N i j = x + y * I := ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [h]
    split_ifs <;> match_scalars <;> simp <;> ring_nf <;> simp

variable {D : D7} {pS pT : D.what₂.Tau → ℕ} {τ : D.what₂.Tau}
  {d : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ →+ Module.End ℂ M} {c : D.what₂.Tau → ℂ} {G : Module.End ℂ M}
  {E : MvPolynomial (FVar D m n) ℂ →ₗ[ℂ] M}

theorem quad_of_comm (hS : IsPMat (pS τ) YS) (hT : IsPMat (pT τ) YT)
    (hd : ∀ ρ (t : ℝ) z, d ρ ((t : ℂ) • z) = (t : ℂ) • d ρ z) (hc : ∀ ρ, c ρ ≠ 0)
    (hG : ∀ N g, G (d τ N g) = d τ N (G g) + d τ (act YS YT N) g)
    (hG' : ∀ ρ, ρ ≠ τ → ∀ N g, G (d ρ N g) = d ρ N (G g))
    (hX : ∀ k Q, E (X k * Q) = c k.1 • cre (pS k.1) (pT k.1) (d k.1) (single k.2.1 k.2.2 1) (E Q))
    (hb : ∀ k Q, E (pderiv k Q) = (-c k.1) • ann (pS k.1) (pT k.1) (d k.1) (single k.2.1 k.2.2 1) (E Q)) :
    (∀ ρ N, ann (pS ρ) (pT ρ) (d ρ) N (G (E 1) - E (fockP τ (pS τ) (pT τ) YS YT 1)) = 0) ∧
    (G (E 1) = E (fockP τ (pS τ) (pT τ) YS YT 1) → ∀ P, G (E P) = E (fockP τ (pS τ) (pT τ) YS YT P)) := by
  classical
  have gc : ∀ N g, G (cre (pS τ) (pT τ) (d τ) N g) =
      cre (pS τ) (pT τ) (d τ) N (G g) + ann (pS τ) (pT τ) (d τ) (act YS YT N) g := fun N g => by
    simp only [cre, ann, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, map_sub, map_smul, hG,
      act_cplx hS hT, map_neg, LinearMap.neg_apply]
    module
  have ga : ∀ N g, G (ann (pS τ) (pT τ) (d τ) N g) =
      ann (pS τ) (pT τ) (d τ) N (G g) + cre (pS τ) (pT τ) (d τ) (act YS YT N) g := fun N g => by
    simp only [cre, ann, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hG,
      act_cplx hS hT, map_neg, LinearMap.neg_apply]
    module
  have gc' : ∀ ρ, ρ ≠ τ → ∀ N g, G (cre (pS ρ) (pT ρ) (d ρ) N g) = cre (pS ρ) (pT ρ) (d ρ) N (G g) :=
    fun ρ h N g => by
      simp only [cre, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hG' ρ h]
  have ga' : ∀ ρ, ρ ≠ τ → ∀ N g, G (ann (pS ρ) (pT ρ) (d ρ) N g) = ann (pS ρ) (pT ρ) (d ρ) N (G g) :=
    fun ρ h N g => by
      simp only [ann, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hG' ρ h]
  have hv : ∀ ρ i j, ann (pS ρ) (pT ρ) (d ρ) (single i j 1) (E 1) = 0 := fun ρ i j => by
    have := hb (ρ, i, j) 1
    rw [pderiv_one, map_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left (neg_ne_zero.2 (hc ρ))
  refine ⟨fun ρ N => ?_, fun h1 P => ?_⟩
  · rw [(expand (hd ρ) N).2]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_
    refine (smul_eq_zero.1 ?_).resolve_left (neg_ne_zero.2 (hc ρ))
    rw [map_sub, smul_sub, ← hb (ρ, i, j), pderiv_fockP_one hS hT, sub_eq_zero]
    dsimp only
    split_ifs with h
    · subst h
      have := ga (single i j 1) (E 1)
      rw [hv, map_zero, eq_comm, add_eq_zero_iff_eq_neg] at this
      rw [this, (expand (hd ρ) _).1, neg_smul_neg]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_one (X _), hX, smul_comm]
    · rw [← ga' ρ h, hv, map_zero, map_zero, smul_zero]
  · induction P using MvPolynomial.induction_on with
    | C a => rw [fockP_C, C_eq_smul_one, map_smul, map_smul, h1, map_smul]
    | add p q hp hq => rw [fockOperator_add, map_add, map_add, map_add, hp, hq]
    | mul_X p k hp =>
      obtain ⟨ρ, i, j⟩ := k
      rw [mul_comm, fockP_X_mul hS hT, map_sub, hX, hX, map_smul, ← hp]
      dsimp only
      split_ifs with h
      · subst h
        rw [gc, smul_add, sub_eq_add_neg, (expand (hd ρ) (act YS YT _)).2]
        congr 1
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, hb,
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        module
      · rw [gc' ρ h, map_zero, sub_zero]

end Ops

section Laws

open GlobalTheory.FockCompare GlobalTheory.FockIndep GlobalTheory.OrientedHeis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T V W : HSp D}

theorem fockScale_sq (τ : D.what₂.Tau) :
    (fockScale D τ : ℂ) * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
  have h1 := xi_zero_im_pos D τ
  have h2 : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im := by
    rw [← Complex.abs_im_eq_norm.2 (GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ), abs_of_pos h1]
  have h3 := Real.mul_self_sqrt (x := 2 * Real.pi * (tauE D τ D.host.xi0).im) (by positivity)
  have h4 : fockScale D τ * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
    rw [fockScale, h2]; linear_combination 4 * h3
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h4

theorem fockScale_ne (τ : D.what₂.Tau) : (fockScale D τ : ℂ) ≠ 0 := by
  intro h
  have h1 := fockScale_sq (D := D) τ
  have h2 := xi_zero_im_pos D τ
  rw [h, mul_zero] at h1
  have h3 : (0 : ℝ) = 8 * Real.pi * (tauE D τ D.host.xi0).im := by exact_mod_cast h1
  have : (0 : ℝ) < 8 * Real.pi * (tauE D τ D.host.xi0).im := by positivity
  exact this.ne h3

variable (V W) in

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) : Submodule ℂ (WO V W → ℂ) where
  carrier := {g | IsThetaFunO ψ V W g}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

open Classical in
theorem dRho_dir_add (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z + z') f = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z' f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ (z + z') 1) = piW θ T S (lineAt θ τ z 1) + piW θ T S (lineAt θ τ z' 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, piW_lineAt hθ, Pi.single_add]
    rfl
  funext w
  rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_add, ContinuousLinearMap.map_add]
  push_cast
  ring

open Classical in
theorem dRho_dir_smul (τ : D.what₂.Tau) (t : ℝ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ ((t : ℂ) • z) f = (t : ℂ) • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ ((t : ℂ) • z) 1) = t • piW θ T S (lineAt θ τ z 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, Pi.single_smul]
    rfl
  funext w
  rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

end Laws

section Model

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem onb_diag {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) :
    Bᴴ * G * B = diagonal (sg p) ∧ s * B = B * diagonal (sg p) ∧ IsUnit B.det := by
  obtain ⟨ε, h0, h1, h2⟩ := h
  have e : (fun a => (ε a : ℂ)) = sg p := funext fun a => by
    rcases h0 a with h | h
    · simp [sg, h.1, h.2]
    · simp [sg, h.1, not_lt.2 h.2]
  rw [e] at h1 h2
  refine ⟨h1, h2, Matrix.isUnit_det_of_left_inverse (B := diagonal (sg p) * (Bᴴ * G)) ?_⟩
  rw [Matrix.mul_assoc, h1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sg
  split_ifs <;> simp

theorem cplxO_conj {m n p p' : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} {G' s' B' : Matrix (Fin m) (Fin m) ℂ}
    (h : IsONBasis G s B p) (h' : IsONBasis G' s' B' p') (N : Matrix (Fin m) (Fin n) ℂ) :
    cplxO s s' (B' * N * B⁻¹) = B' * cplx p p' N * B⁻¹ := by
  obtain ⟨-, h1, hB⟩ := onb_diag h
  have e : B⁻¹ * s = diagonal (sg p) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = _ := by rw [h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]
  unfold cplx cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc s', Matrix.mul_assoc _ B⁻¹, e, ← Matrix.mul_assoc s',
    ← Matrix.mul_assoc s', (onb_diag h').2.1]
  simp only [Matrix.mul_assoc]

theorem act_conj {m n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} {B' : Matrix (Fin m) (Fin m) ℂ} (h : IsUnit B.det)
    (h' : IsUnit B'.det) (YS : Matrix (Fin n) (Fin n) ℂ) (YT : Matrix (Fin m) (Fin m) ℂ)
    (N : Matrix (Fin m) (Fin n) ℂ) :
    B' * YT * B'⁻¹ * (B' * N * B⁻¹) - B' * N * B⁻¹ * (B * YS * B⁻¹) = B' * act YS YT N * B⁻¹ := by
  simp only [act, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ h,
    Matrix.nonsing_inv_mul_cancel_left _ _ h']

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

def der (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ →+ Module.End ℂ (thetaSub S T ψ) :=
  AddMonoidHom.mk' (fun N =>
    { toFun := fun g => ⟨Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (B' * N * B⁻¹) g, theta_dRho hθ hψ τ _ g.2⟩
      map_add' := fun g g' => Subtype.ext (dRho_add hψ hθ τ _ g.2 g'.2)
      map_smul' := fun c g => Subtype.ext (dRho_smul hψ hθ τ _ c g.2) }) fun N N' =>
    LinearMap.ext fun g => Subtype.ext (by
      have := dRho_dir_add hψ hθ τ (B' * N * B⁻¹) (B' * N' * B⁻¹) g.2
      rw [← Matrix.add_mul, ← Matrix.mul_add] at this
      exact this)

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
  {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {pS pT : D.what₂.Tau → ℕ}
  (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
  (bS : ∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) (bT : ∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ))
include hψ hθ hS hT bS bT

open Classical in

theorem ccr (k l : FVar D T.rank S.rank) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT l g) =
    aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT l
      (annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g) +
      (if k = l then -(fockScale D k.1 : ℂ) else 0) • g := by
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', c, d⟩ := l
  refine (annih_aPlus hψ hθ τ _ hS hT τ' _ hg).trans ?_
  refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
  unfold omDir
  by_cases h : τ = τ'
  · subst h
    have sq : ∀ a : Fin S.rank, sg (pS τ) a * sg (pS τ) a = 1 := fun a => by
      unfold sg
      split_ifs <;> simp
    simp only [if_true, GlobalTheory.FockVecInj.cplxO_unitMap (onb_diag (bS τ)).2.2 (onb_diag (bS τ)).2.1 (onb_diag (bT τ)).2.1,
      Matrix.mul_smul, Matrix.trace_smul, GlobalTheory.FockVecInj.trace_unitMap sq (onb_diag (bS τ)).1 (onb_diag (bT τ)).1,
      Prod.mk.injEq, true_and]
    have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
    have h1 := fockScale_sq (D := D) τ
    have h2 := fockScale_ne (D := D) τ
    by_cases e : a = c ∧ b = d
    · rw [if_pos e, if_pos e, inv_mul_eq_iff_eq_mul₀ h2, mul_neg, h1]
      unfold sg
      split_ifs <;> simp [hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [e]
  · simp [h]

theorem annih_pure {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) (k : FVar D T.rank S.rank)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)
      (pureTensorO ψ θ S T sS sT BS BT f Q) =
      (-(fockScale D k.1 : ℂ)) • pureTensorO ψ θ S T sS sT BS BT f (pderiv k Q) := by
  classical
  unfold pureTensorO
  have hm := pure_mem (A := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf
  have hX := pure_X_mul (A := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) (fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
    (fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h') (fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h) hf
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [C_eq_smul_one, map_smul, pure_one, annih_smul hψ hθ _ _ _ _ hf, hv, Derivation.map_smul, pderiv_one, smul_zero,
      smul_zero, map_zero, smul_zero]
  | add p q hp hq => rw [map_add, annih_add hψ hθ _ _ _ (hm _) (hm _), hp, hq, map_add, map_add, smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, ccr hψ hθ hS hT bS bT _ _ (hm _), hp, pderiv_mul, map_add, hX, pderiv_X, add_comm, smul_add]
    refine congrArg₂ (· + ·) ?_ (aPlus_smul hψ hθ _ _ _ _ (hm _))
    by_cases h : k = j
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]

end Model

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis in

theorem acts_by_fockP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Gn : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (BT τ * YT * (BT τ)⁻¹ * u - u * (BS τ * YS * (BS τ)⁻¹)) f) ∧ ∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → (∀ g, IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ipO μ 𝓕 (Gn f) g = 0) → ∀ P, Gn (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT f (fockP τ (pS τ) (pT τ) YS YT P) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT _ _ hS hT bS bT τ YS YT yS yT μ 𝓕 hμ Gn hG f hf hv h0
  have hm := pure_mem (A := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf
  have hX := pure_X_mul (A := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) (fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
    (fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h') (fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h) hf
  let E : MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] thetaSub S T ψ :=
    (pureTensorO ψ θ S T sS sT BS BT f).codRestrict (thetaSub S T ψ) hm
  let G : Module.End ℂ (thetaSub S T ψ) := Gn.restrict fun g hg => (hG g hg).1
  let d := fun ρ => der hψ hθ ρ (BS ρ) (BT ρ)
  have hE : ∀ Q, (E Q : WO S T → ℂ) = pureTensorO ψ θ S T sS sT BS BT f Q := fun _ => rfl
  have hGc : ∀ g, (G g : WO S T → ℂ) = Gn g := fun _ => rfl
  have hd : ∀ ρ N g, (d ρ N g : WO S T → ℂ) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ ρ (BT ρ * N * (BS ρ)⁻¹) g := fun _ _ _ => rfl
  have hcre : ∀ ρ N g, (cre (pS ρ) (pT ρ) (d ρ) N g : WO S T → ℂ) =
      crea (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) (BT ρ * N * (BS ρ)⁻¹) g := fun ρ N g => by
    rw [crea, cplxO_conj (bS ρ) (bT ρ)]; rfl
  have hann : ∀ ρ N g, (ann (pS ρ) (pT ρ) (d ρ) N g : WO S T → ℂ) =
      annih (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) (BT ρ * N * (BS ρ)⁻¹) g := fun ρ N g => by
    rw [annih, cplxO_conj (bS ρ) (bT ρ)]; rfl
  obtain ⟨k1, k2⟩ := quad_of_comm (d := d) (c := fun ρ => (fockScale D ρ : ℂ)⁻¹) (G := G) (E := E) yS yT
    (fun ρ t z => LinearMap.ext fun g => Subtype.ext (by
      rw [hd, Matrix.mul_smul, Matrix.smul_mul]
      exact dRho_dir_smul hψ hθ ρ t _ g.2))
    (fun ρ => inv_ne_zero (fockScale_ne ρ))
    (fun N g => Subtype.ext (by
      rw [Submodule.coe_add, hGc, hd, hd, hd, hGc, ← act_conj (onb_diag (bS τ)).2.2 (onb_diag (bT τ)).2.2]
      exact eq_add_of_sub_eq' ((hG g g.2).2.1 _)))
    (fun ρ h N g => Subtype.ext ((hG g g.2).2.2 ρ h _))
    (fun k Q => Subtype.ext (by
      rw [Submodule.coe_smul, hcre]
      exact hX Q k))
    (fun k Q => Subtype.ext (by
      have := annih_pure hψ hθ hS hT bS bT hf hv k Q
      rw [unitMap] at this
      rw [Submodule.coe_smul, hann, hE, hE, this, smul_smul, neg_mul_neg, inv_mul_cancel₀ (fockScale_ne _), one_smul]))
  refine fun P => congrArg Subtype.val (k2 ?_ P)
  rw [← sub_eq_zero]
  have e1 : (G (E 1) : WO S T → ℂ) = Gn f := congrArg Gn (pure_one f)
  generalize hF : fockP τ (pS τ) (pT τ) YS YT 1 = F at k1
  generalize hh : G (E 1) - E F = h at k1
  have ht : IsThetaFunO ψ S T h := h.2
  have hvac : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) h := fun ρ z => by
    have := congrArg Subtype.val (k1 ρ ((BT ρ)⁻¹ * z * BS ρ))
    rw [hann, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (onb_diag (bT ρ)).2.2,
      Matrix.mul_nonsing_inv_cancel_right _ _ (onb_diag (bS ρ)).2.2] at this
    exact this
  have ip := fun g (hg : IsThetaFunO ψ S T g) => GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g h hg ht
  have ip' := fun g (hg : IsThetaFunO ψ S T g) => GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ h g ht hg
  let L : thetaSub S T ψ →ₗ[ℂ] ℂ :=
    { toFun := fun g => ipO μ 𝓕 g h
      map_add' := fun g g' => ((ip g g.2).2.2.2.1 g' g'.2).1
      map_smul' := fun c g => ((ip g g.2).2.2.1 c).1 }
  have hL : ∀ g, L g = ipO μ 𝓕 g h := fun _ => rfl
  have l1 : L (G (E 1)) = 0 := by rw [hL, e1]; exact h0 h ht hvac
  have lc : ∀ ρ N g, L (cre (pS ρ) (pT ρ) (d ρ) N g) = 0 := fun ρ N g => by
    have sk : ∀ N, L (d ρ N g) = -ipO μ 𝓕 g (d ρ N h) := fun N =>
      (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ g h g.2 ht ρ _).2
    have z : ipO μ 𝓕 g (ann (pS ρ) (pT ρ) (d ρ) N h : thetaSub S T ψ) = 0 := by
      rw [k1]; simp [ipO]
    rw [ann, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ _ g (d ρ N h).2 g.2).2.2.2.1 _ (I • d ρ _ h).2).2, Submodule.coe_smul,
      ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g _ g.2 (d ρ _ h).2).2.2.1 I).2, conj_I] at z
    rw [cre, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, sk, sk, smul_eq_mul]
    linear_combination -z
  have l2 : L (E F) = 0 := by
    rw [← hF]
    refine fockOperator_one_mem (LinearMap.ker (L ∘ₗ E)) fun y Q => ?_
    have e : E (X y * Q) = (fockScale D y.1 : ℂ)⁻¹ • cre (pS y.1) (pT y.1) (d y.1) (single y.2.1 y.2.2 1) (E Q) :=
      Subtype.ext (by
        rw [Submodule.coe_smul, hcre]
        exact hX Q y)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, e, map_smul, lc, smul_zero]
  have l3 : L h = 0 := by
    have := map_sub L (G (E 1)) (E F)
    rwa [hh, l1, l2, sub_zero] at this
  rw [hL, (ip h ht).2.2.2.2.1] at l3
  exact Subtype.ext ((ip h ht).2.2.2.2.2.1 (Complex.ofReal_eq_zero.1 l3))

end GlobalTheory.FockLieQuad

end
