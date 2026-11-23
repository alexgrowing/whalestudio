import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVectorStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StdProp

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_sigR [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sigR R σ) := by
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  exact this

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem measurableSet_fibre [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] (c : R) :
    MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E | qR R σ J (X 0) = c} :=
  (isClosed_eq (continuous_qR R σ J) continuous_const).measurableSet

omit [FiniteDimensional F E] in
theorem smul_eq_lrAct {n : ℕ} (g : HA R σ J) :
    (fun X : Fin n → Fin M → R ⊗[F] E => g • X) = lrAct (HA.mat R σ J g).val 1 := by
  funext X a
  show (HA.mat R σ J g).val.mulVec (X a) = _
  simp [lrAct, Matrix.one_apply]

end Local

theorem stdX_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b s M J x β ν hJ hβ hx ⟨mi, mv, hi, hv, hP⟩
  obtain ⟨nI, nV⟩ := nice_ainf_fv F
  obtain ⟨qloc, gloc⟩ := q_and_unitary_local_components F E σ M J
  have hβu : IsUnit β := Ne.isUnit hβ
  have bI := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Ainf F) nI M J _ _ _ mi s.haar_nuI (hβu.map _) hi
  have bV := fun v => GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Fv F v) (nV v) M J _ _ _ (mv v) (s.haar_nuV v)
    (hβu.map _) (hv v)
  have pI := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) nI M J x β _ _ mi hJ hβ hx s.haar_lamI s.haar_nuI hi
  have pV := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (nV v) M J x β _ _ (mv v) hJ hβ hx
    (s.haar_lamV v) (s.haar_nuV v) (hv v)
  obtain ⟨hfin, hne, huniq, hsupp⟩ := GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hP
  have h1 : ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 := by
    have := hsupp {X | qR (Ainf F) σ J (X 0) = algebraMap F _ β}
      (fun v => {X | qR (Fv F v) σ J (X 0) = algebraMap F _ β})
      (measurableSet_fibre _ σ J _) (fun v => measurableSet_fibre _ σ J _) bI.1 (fun v => (bV v).1)
    refine measure_mono_null (fun X hX => ?_) this
    exact fun h => hX ((qloc (X 0) β).2 h)
  refine ⟨h1, ?_, ?_, hfin, hne pI.2.2 fun v => (pV v).2.2⟩
  · intro g
    obtain ⟨⟨gi, hgi⟩, hgv⟩ := gloc g
    have hT := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν mi mv (HA.mat (AF F) σ J g) 1 hP
    have e1 : mi.map (lrAct ((HA.mat (AF F) σ J g).val.map prInf)
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map prInf)) = mi := by
      rw [← hgi, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact pI.1 gi
    have e2 : (fun v => (mv v).map (lrAct ((HA.mat (AF F) σ J g).val.map (prV v))
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map (prV v)))) = mv := by
      funext v
      obtain ⟨gv, hgv⟩ := hgv v
      rw [← hgv, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact (pV v).1 gv
    rw [e1, e2, Units.val_one, ← smul_eq_lrAct] at hT
    exact huniq _ hT
  · refine measure_mono_null (fun X hX => ?_) h1
    exact fun h => hX (GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM M J x β hJ hβ hx X h)

end GlobalTheory.GaugeEx.StdProp
