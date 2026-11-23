import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAlg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem inv_mul_gram (V : HSp D) : ((HSpace.gram V)⁻¹.map (incA D)) * ((HSpace.gram V).map (incA D)) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)

theorem gramI_conj (V : HSp D) : (((HSpace.gram V)⁻¹.map (incA D)).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) :=
  GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)

theorem conjT_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (B : Matrix (Fin n) (Fin k) (AE D)) :
    ((A * B).map (cA D))ᵀ = (B.map (cA D))ᵀ * (A.map (cA D))ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_conjT {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) : (((A.map (cA D))ᵀ).map (cA D))ᵀ = A := by
  ext i j; simp [GlobalTheory.DualPairCheck.cA_cA]

theorem adjO_eq (S T : HSp D) (y : WO T S) :
    (adjO S T y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      HMul.hMul (HMul.hMul ((HSpace.gram T)⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose) ((HSpace.gram S).map (incA D)) := rfl

theorem adj_invol (S T : HSp D) (x : WO S T) : adjO S T (adjO T S x) = x := by
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]
  simp only [← Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]

theorem adj_add (S T : HSp D) (y y' : WO T S) : adjO S T (y + y') = adjO S T y + adjO S T y' := by
  rw [adjO_eq, adjO_eq, adjO_eq]
  have e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) =
      (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) := by
    ext i j; simp
  rw [e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hO_eq (S T : HSp D) (x y : WO S T) : hO S T x y = Matrix.trace (adjO T S y * x) := by
  rw [adjO_eq]
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  rw [hO_eq, hO_eq]
  have e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ) := by
    rw [Matrix.trace_transpose]; simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
  rw [e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj,
    adjO_eq, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem hO_adj (S T : HSp D) (x y : WO T S) : hO S T (adjO S T x) (adjO S T y) = hO T S y x := by
  rw [hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]

theorem adj_sympl (S T : HSp D) (y y' : WO T S) :
    symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y' := by
  unfold symplO
  rw [hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_adj (S T : HSp D) (y y' : WO T S) :
    symplOH S T (adjO S T y) (adjO S T y') = -symplOH T S y y' := by
  unfold symplOH; rw [adj_sympl, mul_neg]

end GlobalTheory.AdjLawPf

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem mt_inv_mul (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem conjT_gram (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V g⁻¹ := by
  calc ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * (mt V g * mt V g⁻¹) := by
        rw [mt_mul_inv, Matrix.mul_one]
    _ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]

theorem gramI_conjT (V : HSp D) (h : GA D V) :
    ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = mt V h * ((HSpace.gram V)⁻¹.map (incA D)) := by
  have k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h := by
    rw [conjT_gram, inv_inv]
  calc ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ * (((HSpace.gram V).map (incA D)) * ((HSpace.gram V)⁻¹.map (incA D))) := by
        rw [GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]
    _ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

theorem adj_act (S T : HSp D) (g : GA D S) (h : GA D T) (y : WO T S) :
    adjO S T (actO T S h g y) = actO S T g h (adjO S T y) := by
  unfold actO
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul]
  simp only [← Matrix.mul_assoc]
  rw [gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]
  simp only [Matrix.mul_assoc]

theorem adj_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjO S T (ratW S T γ) = ratW T S (HMul.hMul (HMul.hMul (HSpace.gram T)⁻¹ (γ.map star)ᵀ) (HSpace.gram S)) := by
  have e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D) := by
    ext i j; simp [GlobalTheory.DualPairCheck.cA_incA]
  rw [adjO_eq]
  unfold ratW
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem adj_rat_of (S T : HSp D) (y : WO T S) (hy : y ∈ ratL S T) : adjO S T y ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨_, (adj_ratW S T γ).symm⟩

theorem adj_rat (S T : HSp D) (y : WO T S) : adjO S T y ∈ ratL T S ↔ y ∈ ratL S T :=
  ⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩

theorem adj_half (S T : HSp D) (e : AE D) (y : WO T S) (hy : IsHalf e y) : IsHalf (cA D e) (adjO S T y) := by
  intro i j
  have hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy]
  rw [adjO_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l

theorem adj_cont (S T : HSp D) : Continuous (adjO S T) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ :=
    (continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_infPart (S T : HSp D) (u : WO T S) (hu : u.map (infPart D) = 0) : (adjO S T u).map (infPart D) = 0 := by
  have h0 : ∀ k l, infPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show infPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_finPart (S T : HSp D) (u : WO T S) (hu : u.map (finPart D) = 0) : (adjO S T u).map (finPart D) = 0 := by
  have h0 : ∀ k l, finPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show finPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def adjHom (S T : HSp D) : WO T S →+ WO S T := AddMonoidHom.mk' (adjO S T) (adj_add S T)

theorem conj_psi (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp

theorem adj_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (y : WO T S) (f : WO S T → ℂ) :
    heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f) := by
  funext w
  simp only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]

theorem adj_theta (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (dag S T f) where
  quasi γ w := by
    simp only [dag]
    rw [adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]
    simp only [neg_neg]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩
    rw [adj_heis ψ hψ]
    exact congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))
  cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t))
      (adjO S T w)
    have e : (fun t => dag S T f (w + L t)) =
        fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t)) := by
      funext t; simp [dag, adj_add, adjHom]
    rw [e]
    exact Complex.conjCLE.contDiff.comp h

theorem adjLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  intro D ψ hψ S T
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  exact { invol := adj_invol S T
          add := adj_add S T
          cont := adj_cont S T
          sympl := adj_sympl S T
          act := adj_act S T
          rat := adj_rat S T
          half := adj_half S T
          Heisenberg₂ := adj_heis ψ hn S T
          theta := adj_theta ψ hn S T }

end GlobalTheory.AdjLawPf
