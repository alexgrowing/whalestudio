import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SeeSaw.RealComm

variable {D : D7}

theorem map_mul_gen {A B m n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (u : Matrix m n A) (g : Matrix n n A) :
    (u * g).map φ = u.map φ * g.map φ := Matrix.map_mul

theorem actO_real_fin (S T : HSp D) {z : GA D S} (hz : z ∈ GinfC S) {u : WO S T} (hu : u.map (infPart D) = 0) :
    actO S T z 1 u = u := by
  have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
  have hz' : finHom S z⁻¹ = 1 := (GinfC S).inv_mem hz
  have h2 : (Formalism.L2.Theta.mt S z⁻¹).map (finPart D) = 1 := congrArg Units.val hz'
  rw [actO, h1, Matrix.one_mul]
  have h3 := map_mul_gen (finPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  have h4 := map_mul_gen (infPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  rw [h2, Matrix.mul_one] at h3
  rw [hu, Matrix.zero_mul, ← hu] at h4
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun h4 i) j) (congrFun (congrFun h3 i) j)

theorem om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  intro D ψ S T χS χT om H z hz c hc g hg
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, H.om_heis z 1 u g hg, actO_real_fin S T hz (hc u hu)]

end GlobalTheory.SeeSaw.RealComm
