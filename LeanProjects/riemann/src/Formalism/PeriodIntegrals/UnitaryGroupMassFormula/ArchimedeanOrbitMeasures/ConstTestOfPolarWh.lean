import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperW

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem isOpen_units_tens {D : D7} (X : HidaSetting D) :
    IsOpen {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) (Module.finBasis X.B.I.F X.B.I.E)
  have key : {x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit x} =
      (fun x => (LinearMap.toMatrix B B (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) x)).det) ⁻¹'
        {a | IsUnit a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det]
    constructor
    · intro h; exact h.map (Algebra.lmul (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    · intro h
      obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
      exact isUnit_iff_exists_inv.2 ⟨y, hy⟩
  rw [key]
  refine (PI.AprimeInfW.isOpen_units_Ainf X.B.I.F).preimage (Continuous.matrix_det ?_)
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply]
  change Continuous fun x : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i (x * B j)
  have hc : Continuous fun v : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E => B.coord i v :=
    IsModuleTopology.continuous_of_linearMap (B.coord i)
  exact hc.comp (continuous_mul_const _)

theorem invNbhd_holds : InvNbhd := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : T2Space (MfI X) := inferInstanceAs (T2Space (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
    (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (MfI X) := inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : SecondCountableTopology (MfI X) := inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) →
    Fin (D.R.rS + 1 + D.R.rS) → (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have hU : IsOpen {M : MfI X | IsUnit M} := by
    have e : {M : MfI X | IsUnit M} = (fun M : MfI X => M.det) ⁻¹' {x | IsUnit x} := by
      ext M; exact Matrix.isUnit_iff_isUnit_det M
    rw [e]
    exact (isOpen_units_tens X).preimage (continuous_id.matrix_det)
  have : LocallyCompactSpace (MfI X)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (MfI X)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : MfI X ≃ₜ (MfI X)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (MfI X)ˣ := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hO : MulAction.orbit (MfI X)ˣ (1 : MfI X) = {M : MfI X | IsUnit M} := by
    ext M; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
    · rintro ⟨u, rfl⟩; exact ⟨u, by simp [Units.smul_def]⟩
  have hOo : IsOpen (MulAction.orbit (MfI X)ˣ (1 : MfI X)) := hO ▸ hU
  have : LocallyCompactSpace (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    hOo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul (MfI X)ˣ (MulAction.orbit (MfI X)ˣ (1 : MfI X)) :=
    ⟨continuous_induced_rng.2 (by
      change Continuous fun p : (MfI X)ˣ × MulAction.orbit (MfI X)ˣ (1 : MfI X) => ((p.1 : MfI X) * (p.2 : MfI X))
      exact (Units.continuous_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))⟩
  have y1 : (1 : MfI X) ∈ MulAction.orbit (MfI X)ˣ (1 : MfI X) := MulAction.mem_orbit_self _
  have hopen : IsOpenMap (fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) :=
    isOpenMap_smul_of_sigmaCompact _
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : (MfI X)ˣ)
  have hWo : IsOpen (Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V)) :=
    hOo.isOpenMap_subtype_val _ (hopen _ isOpen_interior)
  have h1W : (1 : MfI X) ∈ Subtype.val '' ((fun u : (MfI X)ˣ => u • (⟨1, y1⟩ : MulAction.orbit (MfI X)ˣ (1 : MfI X))) ''
      interior V) :=
    ⟨⟨1, y1⟩, ⟨1, mem_interior_iff_mem_nhds.2 hV1, one_smul _ _⟩, rfl⟩
  refine ⟨_, hWo.mem_nhds h1W, (fun u : (MfI X)ˣ => ((u⁻¹ : (MfI X)ˣ) : MfI X)) '' V,
    hVc.image Units.continuous_coe_inv, ?_⟩
  rintro b ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨((u⁻¹ : (MfI X)ˣ) : MfI X), ⟨u, interior_subset hu, rfl⟩, ?_⟩
  change ((u⁻¹ : (MfI X)ˣ) : MfI X) * ((u : MfI X) * 1) = 1
  simp

theorem constTest_of_polar_wh (hP : PolarLoc) (hW : WittInf) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar_witt hP hW hH invNbhd_holds

end PI.AprimeInfW
