import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.RowsSign

open MvPolynomial
open scoped ComplexOrder

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem degree_of_colWeight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul_of_weight {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

def totDeg (lam : ι → DomWeight n) : ℕ := ∑ τ, ∑ j, (lam τ).natW j

theorem blockAct_smul_of_mem (lam : ι → DomWeight n) (a : K) (M : ι → Matrix (Fin n) (Fin n) K)
    {y : Formalism.L2.DIV.Pol K ι n} (hy : y ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => a • M τ) y = a ^ totDeg lam • Formalism.GradedWeylDivisibility.blockAct K M y := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have hT := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => a • M τ)).1
    have hT' := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (a • M τ) (F τ)) =
        C (a ^ (∑ j, (lam τ).natW j)) * Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (M τ) (F τ)) := by
      intro τ
      rw [rowAct_smul_of_weight a (M τ) (F τ) (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.1 (hF τ)).1, map_smul, smul_eq_C_mul]
    rw [map_prod, map_prod]
    simp only [hT, hT']
    rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      smul_eq_C_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

variable [StarRing K]

def negSign (lam : ι → DomWeight n) : K := gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * (-1) ^ totDeg lam

theorem pairK_neg (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) :
    pairK lam (fun τ => -G τ) x y = negSign lam * pairK lam G x y := by
  have hy := blockAct_smul_of_mem lam (-1 : K) (fun τ => (G τ)ᵀ) y.2
  have hT : (fun τ => (-G τ)ᵀ) = fun τ => (-1 : K) • (G τ)ᵀ := by
    funext τ
    rw [Matrix.transpose_neg, neg_one_smul]
  have hg : gramTw lam (fun τ => -G τ) = gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam G := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← mul_zpow, ← Matrix.det_mul, neg_mul, one_mul]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul]
  rw [hT, hy, map_smul, hg, negSign, smul_eq_mul]
  ring

theorem negSign_mul_self (lam : ι → DomWeight n) : negSign (K := K) lam * negSign lam = 1 := by
  have hd : ((-1 : Matrix (Fin n) (Fin n) K)).det * ((-1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [← Matrix.det_mul, neg_mul_neg, one_mul, Matrix.det_one]
  have hz : ∀ e : ℤ, ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e * ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e = 1 := by
    intro e
    rw [← mul_zpow, hd, _root_.one_zpow]
  have hp : ((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => hz _
  calc negSign (K := K) lam * negSign lam
      = (gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K))) *
        (((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam) := by unfold negSign; ring
    _ = 1 := by rw [hgg, hp, one_mul]

end General

end GlobalTheory.RowsSign

namespace GlobalTheory.RowsSign

open scoped ComplexOrder InnerProductSpace

theorem pairV_neg_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (φ : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h : ∀ x y, inner ℂ (c0 x) (c0 y) = φ (pairV emb lam (-1) x y)) :
    ∀ x y, pairV emb lam (-1) x y = pairV emb lam 1 x y := by
  have hG : gramK emb (-1 : Matrix (Fin n) (Fin n) E) = fun τ => -(gramK emb 1 τ) := by
    funext τ
    ext i j
    simp [gramK, Matrix.neg_apply, Matrix.one_apply]
  have hneg : ∀ x y, pairV emb lam (-1) x y = negSign lam * pairV emb lam 1 x y := by
    intro x y
    unfold pairV
    rw [hG, pairK_neg]
  by_cases hnt : Nontrivial (VV K lam)
  · rcases mul_self_eq_one_iff.1 (negSign_mul_self (K := K) lam) with hc | hc
    · intro x y
      rw [hneg, hc, one_mul]
    · exfalso
      have hpos := Formalism.L2.DIV.pairPos K ι n lam (gramK emb 1) φ (fun τ => by
        have : ((gramK emb (1 : Matrix (Fin n) (Fin n) E) τ).map φ) = 1 := by
          ext i j
          simp [gramK, Matrix.one_apply]
        rw [this]
        exact Matrix.PosDef.one)
      obtain ⟨i⟩ := (bVV K lam).index_nonempty
      have h1 := hpos.diag_pos (i := i)
      simp only [Matrix.of_apply] at h1
      have h2 := h (bVV K lam i) (bVV K lam i)
      rw [hneg, hc, neg_one_mul, map_neg] at h2
      have h3 := inner_self_nonneg (𝕜 := ℂ) (x := c0 (bVV K lam i))
      rw [h2, map_neg, RCLike.re_to_complex] at h3
      have h4 := (Complex.lt_def.1 h1).1
      have h5 : (φ (pairV emb lam 1 (bVV K lam i) (bVV K lam i))).re =
          (φ (pairK lam (gramK emb 1) (bVV K lam i) (bVV K lam i))).re := rfl
      simp only [Complex.zero_re] at h4
      linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    intro x y
    rw [Subsingleton.elim x 0]
    simp

end GlobalTheory.RowsSign

open GlobalTheory.RowsSign in
theorem GlobalTheory.RowsSign.pairV_gramR_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W), cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) → Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) → (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) → ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR x y = pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) X.toD7.sp.X'.gram x y := by
  intro X px I hI cX gramR c0R hcX hg htie hinner x y
  have hJ : X.toD7.sp.X'.gram = 1 := by
    obtain ⟨hs, -, h2, -⟩ := hI.spaces
    change X.B.sp.X'.gram = 1
    rw [h2]
    refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
    simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]
  rcases hg with rfl | rfl
  · rfl
  · rw [hJ] at hinner ⊢
    exact pairV_neg_one_eq _ _ _ c0R hinner x y
