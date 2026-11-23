import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem gram_mul_inv (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹ =
      ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  have h2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel, GlobalTheory.LatMoveStd.mt_one'']
  calc V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹
      = (((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g) * Formalism.L2.Theta.mt V g⁻¹ := by rw [h]
    _ = _ := by rw [Matrix.mul_assoc _ (Formalism.L2.Theta.mt V g), h2, Matrix.mul_one]

theorem row_move (V : HSp D) (g : Formalism.L2.Theta.GA D V) (s : Fin V.rank → D.host.E) (j : Fin V.rank) :
    ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) := by
  have e1 : (fun m => incA D (∑ k, star (s k) * V.gram k m)) =
      (fun k => cA D (incA D (s k))) ᵥ* V.gram.map (incA D) := by
    funext m
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply, GlobalTheory.FinPl.FrameLat.cA_incA]
  have e2 : (fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) =
      (Formalism.L2.Theta.mt V g).map (cA D) *ᵥ fun k => cA D (incA D (s k)) := by
    funext m
    exact RingHom.map_mulVec (cA D) _ _ m
  have lhs : ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ((fun m => incA D (∑ k, star (s k) * V.gram k m)) ᵥ* Formalism.L2.Theta.mt V g⁻¹) j := rfl
  have rhs : ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) =
      ((fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) ᵥ* V.gram.map (incA D)) j := rfl
  rw [lhs, rhs, e1, e2, Matrix.vecMul_vecMul, gram_mul_inv, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem act_gen_apply (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((Formalism.L2.Theta.mt T h *ᵥ fun k => incA D (t k)) i *
        ∑ m, cA D ((Formalism.L2.Theta.mt S g *ᵥ fun k => incA D (s k)) m) * incA D (S.gram m j)) := by
  rw [← row_move]
  simp only [actO, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq]
  simp only [ Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem comb_apply (S T : HSp D) (α : Af D.host.F) (a : D.host.E) {m m' : ℕ} (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E)
    (β' : Fin m' → Formalism.L2.Theta.AE D) (b' : Fin m' → Fin S.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    (∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * b p i * ∑ k, star (b' q k) * S.gram k j)) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((∑ p, β p * incA D (b p i)) *
        ∑ k, cA D (∑ q, β' q * incA D (b' q k)) * incA D (S.gram k j)) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, GlobalTheory.LatMoveStd.gen_eq]
  simp only [map_sum, map_mul,
    GlobalTheory.FinPl.FrameLat.cA_incA, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_)
  ring

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen

set_option synthInstance.maxHeartbeats 400000 in

theorem actO_mem_latO : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T g h AS BS AT BT hS hT w hw
  let Ψ : WO S T →+ WO S T :=
    { toFun := actO S T g h
      map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
  have key : latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True) ≤
      (latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨m', β', b', hβ', hb', hu⟩ := hS s hs
    obtain ⟨m, β, b, hβ, hb, hv⟩ := hT t ht
    have e : actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        ∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * b p i * ∑ k, star (b' q k) * S.gram k j) : WO S T) := by
      ext i j
      rw [act_gen_apply, comb_apply, mul_comm, mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] a),
        GlobalTheory.LatticeStable.mul_pair_tmul, GlobalTheory.LatticeStable.mul_pair_tmul]
      congr 2
      simp only [map_mul, map_sum, GlobalTheory.FinPl.FrameLat.finPart_cA, hv, hu]
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show actO S T g h _ ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)
    rw [e]
    refine sum_mem fun p _ => sum_mem fun q _ => ?_
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (AddSubgroup.subset_closure
      ⟨α, hα, fun _ h => absurd trivial h, a, ha, b' q, hb' q, b p, hb p, rfl⟩)
    rw [map_mul]
    exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (hβ p) ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (hβ' q))
  exact key hw

end GlobalTheory.LatMoveGen
