import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorNegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumPsiValuesEqTauProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorTensorPowerCorrespondsFormalSumStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal
open GlobalTheory.TensAct
open ReciprocityTheory.ChartRestriction.G.DVR (cP cPoint_add)

theorem triv_span {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (hB : D.TauBimult) {c : Vec r →₀ ℤ}
    (hc : c ∈ Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)) : Triv T c := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor R D D' W T hB _ _ _
  | zero => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
  | add x y _ _ hx hy => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ hx hy
  | smul n x _ hx =>
    induction n using Int.induction_on with
    | zero => rw [zero_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
    | succ k ih => rw [add_smul, one_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih hx
    | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih (GlobalTheory.T.isStronglyTrivialFormalSumTensor_neg R D D' W T _ hx)

theorem tau_tens {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {z : (TK R).left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' = isoV T.w z J J' (cP D' (TK R) (p + q)).left * qv T z J (p + q) *
      (isoV T.w z J J' (cP D' (TK R) p).left * qv T z J p)⁻¹ *
      (isoV T.w z J J' (cP D' (TK R) q).left * qv T z J q)⁻¹ * (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ']
  rfl

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  intro R _ _ I D D' r W T A A' hA u' hu' hn' y y'
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := triv_span T D.tau_bimult (GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta W A A' hA)
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at D.toPre.P.isLB z
  have key := GlobalTheory.T.rosatiGenerator_tensorPower_corresponds_formalSum R D.toPre D'.toPre W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', GlobalTheory.T.rosatiBalanceFormalSum_psiValues_eq_tauProduct R D.toPre D'.toPre W T D.tau_bimult A A' z J hJ y y'] at key
  have pr := prod_ros (matAct T A) (matAct T A') (cP D'.toPre (TK R) y) (cP D'.toPre (TK R) y')
    (isoV T.w z J J')
  have l₁ : cP D'.toPre (TK R) y ≫ matAct T A = cP D'.toPre (TK R) (latAct T A y) := by
    rw [cP, cP, c_lin, Category.assoc]
  have l₂ : cP D'.toPre (TK R) y' ≫ matAct T A' = cP D'.toPre (TK R) (latAct T A' y') := by
    rw [cP, cP, c_lin, Category.assoc]
  rw [l₁, l₂, ← cPoint_add, ← cPoint_add] at pr
  change ∏ a, isoV T.w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (matAct T A) (matAct T A') a) ^ rosatiε a = _ at pr
  rw [pr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_tens T hJ hJ', tau_tens T hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have r0 : rosLat T A A' y y' 0 = latAct T A y + y' := rfl
  have r1 : rosLat T A A' y y' 1 = latAct T A y := rfl
  have r2 : rosLat T A A' y y' 2 = y' := rfl
  have r3 : rosLat T A A' y y' 3 = y + latAct T A' y' := rfl
  have r4 : rosLat T A A' y y' 4 = y := rfl
  have r5 : rosLat T A A' y y' 5 = latAct T A' y' := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, r0, r1, r2, r3, r4, r5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'

end GlobalTheory.TensBal
