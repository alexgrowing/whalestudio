import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMean

variable {D : D7} {A B : HSp D}

def thetaMean {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T))
    (f : WO S T → ℂ) : GA D S → ℂ :=
  fun g => ⨍ q, AutomorphicL2Unitary.descend (GQ T) (fun h => thetaKO ω g h f) q ∂autMeasure T ν

theorem lagr_add (z z' : WO A B) : lagr A B (z + z') = lagr A B z + lagr A B z' := Matrix.ext fun i k => by
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
    simp only [Matrix.add_apply, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_add]

theorem lagr_rat (γ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) :
    lagr A B (rat γ) = ratW B (dblSp A) (Matrix.of fun i => pairVec finSumFinEquiv (γ i) (-(γ i))) :=
  Matrix.ext fun i k => by
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [lagr, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, ratW, rat, Matrix.of_apply,
        Matrix.map_apply, pairVec_inl, pairVec_inr, Pi.neg_apply,
        map_neg]

theorem continuous_lagr : Continuous (lagr A B) := continuous_matrix fun i k => by
  obtain ⟨i1, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective k
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact continuous_id.matrix_elem i j
  · simp only [lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    exact (continuous_neg (G := WO A B)).matrix_elem i j

theorem hO_lagr (z z' : WO A B) : hO (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, lagr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg, neg_zero,
    Finset.sum_neg_distrib, add_neg_cancel]

theorem symplOH_lagr (z z' : WO A B) : symplOH (dblSp A) B (lagr A B z) (lagr A B z') = 0 := by
  rw [symplOH, symplO, hO_lagr, mul_zero, map_zero, mul_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}

section Zero

variable {f : WO (dblSp A) B → ℂ} {μ μ' : Measure (WO A B)} {𝓨 𝓨' : Set (WO A B)}
  {ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)}

theorem periodic_lagr (hf : IsThetaFunO ψ (dblSp A) B f) :
    ∀ γ ∈ ratMx D B.rank A.rank, ∀ z, f (lagr A B (γ + z)) = f (lagr A B z) := by
  rintro _ ⟨γ, rfl⟩ z
  change f (lagr A B (rat γ + z)) = _
  rw [lagr_add, lagr_rat, hf.quasi, ← lagr_rat, symplOH_lagr, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrableOn_lagr (hμ : IsCovolOne (ratL B A) μ 𝓨) (hf : IsThetaFunO ψ (dblSp A) B f) :
    IntegrableOn (fun z => f (lagr A B z)) 𝓨 μ :=
  covolOne_integrableOn hμ _ (hf.cont.comp continuous_lagr) (periodic_lagr hf)

end Zero

variable {S T : HSp D} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}
  (hω : IsWeilDatumO ψ S T χ χ' ω) (hf : IsThetaFunO ψ S T f)
include hω hf

theorem leftInv_theta (g : GA D S) : LeftInv (GQ T) fun h => thetaKO ω g h f := fun γ hγ h => by
  have := hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres (g, h) f hf)
  rwa [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at this

variable {ν : Measure (GA D T)} [ν.IsHaarMeasure]

theorem integrable_theta (hT : ∃ K : Set (GA D T), IsCompact K ∧ ∀ h, ∃ γ ∈ GQ T, ∃ k ∈ K, h = γ * k) (g : GA D S) :
    Integrable (AutomorphicL2Unitary.descend (GQ T) fun h => thetaKO ω g h f) (autMeasure T ν) := by
  obtain ⟨K, hK, hc⟩ := hT
  have h1 : Continuous fun h => thetaKO ω g h f := (hω.om_cont f hf 0).comp (Continuous.prodMk_right g)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn h1.continuousOn
  refine Integrable.of_bound ?_ C (.of_forall fun q => ?_)
  · refine aestronglyMeasurable_quotMeasure_iff_lift.2 ?_
    rw [show lift (GQ T) (AutomorphicL2Unitary.descend (GQ T) fun h => thetaKO ω g h f) = _ from
      funext (leftInv_theta hω hf g).descend_mk]
    exact h1.measurable.aestronglyMeasurable
  · obtain ⟨γ, hγ, k, hk, e⟩ := hc q.out
    rw [AutomorphicL2Unitary.descend, e]
    exact (congrArg norm (leftInv_theta hω hf g γ hγ k)).trans_le (hC k hk)

theorem thetaMean_eq {𝓕 : Set (GA D T)} (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) (g : GA D S) :
    thetaMean ω ν f g = ⨍ h in 𝓕, thetaKO ω g h f ∂ν := by
  rw [thetaMean, average_eq, setAverage_eq, integral_quotMeasure h𝓕, measureReal_def, quotMeasure_univ h𝓕]
  simp only [(leftInv_theta hω hf g).descend_mk, measureReal_def]

end GlobalTheory.ThetaMean

namespace GlobalTheory.Published

open GlobalTheory.ThetaMean

def SiegelWeilAnisotropicUnitary : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 1 ≤ B.rank → IsAniso B →
  ∀ (χB : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χB ω →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (μ : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) μ 𝓨 →
  ∀ ν : Measure (GA D B), ν.IsHaarMeasure →
  ∀ f : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B f → IsKFinVec ω (Khat A a) f →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν)) ∧
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν f)

end GlobalTheory.Published

end
