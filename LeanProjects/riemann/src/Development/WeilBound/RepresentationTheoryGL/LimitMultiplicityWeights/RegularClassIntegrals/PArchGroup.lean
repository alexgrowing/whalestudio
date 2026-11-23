import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.PArchGroup

theorem cT_star' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem isUnit_of_form {n : ℕ} {J M : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (h : Mᴴ * J * M = J) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h2
  exact hJ.ne_zero h2.symm

theorem isClosed_form {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * J * M = J} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

end MainStatements.WeightKernel.PArchGroup

namespace MainStatements.WeightKernel

open PArchGroup in
theorem archGroup : ArchGroup := by
  intro D V w τ
  have h := isCMExt_host D
  have hu : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
  have hJ : IsUnit (V.gram.map τ.1).det := by
    rw [show V.gram.map τ.1 = τ.1.mapMatrix V.gram from rfl, ← RingHom.map_det]
    exact hu.map _
  have hr : ∀ M, M ∈ Set.range (archMat D.sp.cm.sig V.gram τ) ↔ Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1 := by
    intro M
    constructor
    · rintro ⟨g, rfl⟩
      rw [archMat_eq_archEquiv V.gram h τ g, ← cT_star']
      exact (archEquiv V.gram h τ g).2
    · intro hM
      have hU := isUnit_of_form hJ hM
      have hmem : hU.unit ∈ Formalism.UG.UJ (starRingEnd ℂ) (V.gram.map τ.1) := by
        change Formalism.UG.cT (starRingEnd ℂ) (hU.unit : Matrix (Fin _) (Fin _) ℂ) * V.gram.map τ.1 *
          (hU.unit : Matrix (Fin _) (Fin _) ℂ) = V.gram.map τ.1
        rw [cT_star', IsUnit.unit_spec]
        exact hM
      refine ⟨(archEquiv V.gram h τ).symm ⟨hU.unit, hmem⟩, ?_⟩
      rw [archMat_eq_archEquiv V.gram h τ, MulEquiv.apply_symm_apply]
      exact IsUnit.unit_spec hU
  refine ⟨hJ, ⟨isEmbedding_archMat V.gram h τ, ?_⟩, hr⟩
  have : Set.range (matCoord (archMat D.sp.cm.sig V.gram τ)) =
      {M : Matrix (Fin _) (Fin _) ℂ | Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1} := by
    ext M
    exact hr M
  rw [this]
  exact isClosed_form _

end MainStatements.WeightKernel

end
