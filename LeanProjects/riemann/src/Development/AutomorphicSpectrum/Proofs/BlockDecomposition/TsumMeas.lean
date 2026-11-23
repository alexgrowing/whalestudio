import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

abbrev rt (ξ : Matrix (Fin ρ) (Fin p) D.host.E) : Mx D ρ p := ξ.map (incA D)

def chv (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y : Mx D ρ p) : ℂ :=
  ψ (trA (Matrix.trace (pr b₀ x y)))

def jc (y x : Mx D ρ p) : hermA D ρ :=
  ⟨(HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ), by
    have key : ∀ a b : Mx D ρ p, adj (HMul.hMul a (adj b) : Mx D ρ ρ) = (HMul.hMul b (adj a) : Mx D ρ ρ) := by
      intro a b
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
        Formalism.L2.Theta.cA_cA]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    show adj _ = _
    have : adj ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ)) = adj (HMul.hMul y (adj x) : Mx D ρ ρ) + adj (HMul.hMul x (adj y) : Mx D ρ ρ) := by
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add]
    rw [this, key, key, add_comm]⟩

def dsum (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) : ℂ :=
  ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * Φ (rt ξ + y)

def Ap (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (v : Mx D ρ p × Mx D ρ p) : ℂ :=
  dsum ψ b₀ Φ v.2 v.1 * conj (dsum ψ b₀ φ v.2 v.1)

theorem th_zero (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) :
    th ψ b₀ φ 0 x y = dsum ψ b₀ φ x y := by
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have : (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) (0 : hermA D ρ).1 : Mx D ρ ρ)) = 0 := by
      simp
    rw [chz, this]
    simp [halfTr, trA]
  rw [th, h0, one_mul]
  rfl

theorem tsum_meas {ι X : Type} [Countable ι] [MeasurableSpace X] {f : ι → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a := by
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) a => ∑ i ∈ s, f i a) (fun s => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hf i
  · exact tendsto_pi_nhds.2 fun a => (hs a).hasSum

end GlobalTheory.CompanionTheory.FJE
