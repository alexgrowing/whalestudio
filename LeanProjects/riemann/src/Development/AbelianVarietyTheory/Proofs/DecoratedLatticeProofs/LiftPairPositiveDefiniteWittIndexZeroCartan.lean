import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.PairSetting

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  intro D G _ _ Pl0 T' A Ks _ _ _ R F hC _ i σ
  have hi1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left 1 _
  have hi2 : (i : ℕ) + 1 ≤ D.R.m := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ hi1 hi2
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hi1 hi2
  have hk := D.R.rank_add_five_le
  have hm := D.R.two_le_m
  obtain ⟨cA, hF, hcart, hJ, hA0⟩ := GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin D R.θ hC.models.inf (Wc D i) (D.sp.W_sig _) _ (R.MW i σ)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig (↑i + 1) (tauE D τ)
    rw [hC.models.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine ⟨GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef (D.sp.V_sig _) (hC.models.vpos i)), ?_, cA, ⟨?_, ?_, ?_, hC.models.inf, D.sp.W_sig _, hF, hcart, fun τ => ⟨by simp, by simp, by simpa using hpos τ⟩, hJ⟩, ?_⟩
  · rw [hW]; simp only [Ranks.r] at *; omega
  · rw [hW]; simp only [Ranks.r] at *; omega
  · simp only [Ranks.r] at *; omega
  · rw [hV, hW]; rfl
  · intro U hU v
    exact hA0 _ _ U hU (fun ρ => v ρ) (fun τ => GlobalTheory.T.lowestKType_mem_discreteSeriesKFiniteVectors D (Wc D i) _ (R.MW i σ) τ (v τ))

end GlobalTheory.PairSetting
