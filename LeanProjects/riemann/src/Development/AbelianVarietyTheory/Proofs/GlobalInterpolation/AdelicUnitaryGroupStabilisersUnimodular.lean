import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RestrHomSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.GaugeEx
open GlobalTheory.UnitVectorStabiliser GlobalTheory.HermLineZeros
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelicStabUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_stepData (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    (hJ : IsHermND σ J) (x : Fin 1 → Fin (M + 1) → E) (hx : hE σ J (x 0) (x 0) ≠ 0) :
    ∃ (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      StepData σ J x a B J' := by
  have herm := hf_herm (σ : E →+* E) J (conj_invol h) hJ.1
  obtain ⟨a, ha⟩ := exists_of_fixed h (hE σ J (x 0) (x 0)) (herm _ _)
  let φ := hfLin (σ : E →+* E) J (x 0)
  have hφ : φ ≠ 0 := fun h0 => hx (LinearMap.congr_fun h0 (x 0))
  have hk : Module.finrank E (LinearMap.ker φ) = M := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fin_fun] at this
    omega
  let b := Module.finBasisOfFinrankEq E _ hk
  let B : Matrix (Fin (M + 1)) (Fin M) E := Matrix.of fun i j => (b j : Fin (M + 1) → E) i
  have hG : ∀ i j, (Formalism.UG.cT (σ : E →+* E) B * J * B) i j =
      Formalism.UG.hform (σ : E →+* E) J (b i) (b j) := fun i j => by
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  refine ⟨a, B, _, hJ, ?_, ha.symm, fun j => (b j).2, rfl, fun i j => ?_, fun hd => ?_⟩
  · rintro rfl
    exact hx (by rw [← ha, map_zero])
  · rw [hG, hG]
    exact herm _ _
  · obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let y : LinearMap.ker φ := ∑ j, c j • b j
    have h1 : ∀ i, hfLin (σ : E →+* E) J y (b i) = 0 := fun i => by
      have h2 : hfLin (σ : E →+* E) J (b i) y = 0 := by
        rw [← show _ = (0 : E) from congrFun hc0 i]
        simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Matrix.mulVec,
          dotProduct, hG, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact (herm _ _).symm.trans ((congrArg _ h2).trans (map_zero _))
    have h3 : ∀ z : LinearMap.ker φ, hfLin (σ : E →+* E) J y z = 0 := fun z =>
      LinearMap.congr_fun (b.ext (f₁ := hfLin (σ : E →+* E) J y ∘ₗ Submodule.subtype _) (f₂ := 0) h1) z
    have h4 : hfLin (σ : E →+* E) J y (x 0) = 0 :=
      (herm _ _).symm.trans ((congrArg _ (show Formalism.UG.hform _ J (x 0) y = 0 from y.2)).trans (map_zero _))
    obtain ⟨t, p, hp, -⟩ := exists_proj (σ : E →+* E) J (x 0) hx.isUnit (LinearMap.ker φ) fun _ => Iff.rfl
    have h5 : ∀ z, Formalism.UG.hform (σ : E →+* E) J z y = 0 := fun z => by
      have : hfLin (σ : E →+* E) J y z = 0 := by
        rw [hp z, map_add, map_smul, h3, h4, smul_zero, add_zero]
      exact (herm _ _).symm.trans ((congrArg _ this).trans (map_zero _))
    have h6 : J *ᵥ (y : Fin (M + 1) → E) = 0 := funext fun i => by
      have := h5 (Pi.single i 1)
      rw [hf_eq] at this
      simpa [dotProduct, Pi.single_apply, apply_ite] using this
    have h7 : y = 0 := Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h6)
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h7))

theorem isUnimodularLC_of_equiv {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [MeasurableSpace H]
    (hH : IsUnimodularLC H) (e : G ≃* H) (h1 : Continuous e) (h2 : Continuous e.symm) :
    IsUnimodularLC G := by
  obtain ⟨_, _, _, _, _, -, hH⟩ := hH
  let e' : G ≃ₜ H := ⟨e.toEquiv, h1, h2⟩
  haveI := e'.isEmbedding.t2Space
  haveI := e'.isClosedEmbedding.locallyCompactSpace
  haveI := e'.secondCountableTopology
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ hμ => ⟨fun g => ?_⟩⟩
  haveI := hH _ (MulEquiv.isHaarMeasure_map μ e h1 h2)
  have h3 := congrArg (Measure.map e.symm) (map_mul_right_eq_self (μ.map e) (e g))
  rw [Measure.map_map h2.measurable h1.measurable,
    Measure.map_map (measurable_mul_const _) h1.measurable,
    Measure.map_map h2.measurable ((measurable_mul_const _).comp h1.measurable)] at h3
  convert h3 using 1
  · congr 1
    funext y
    simp
  · rw [show e.symm ∘ e = id from funext fun y => by simp, Measure.map_id]

theorem unimodularOver_of_forall (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R]
    (hR : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA R σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : UnimodularOver R σ J := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsUnimodularLC (HA R σ J) :=
    fun M J hJ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨Measure.haar, inferInstance⟩, hR M J hJ⟩
  refine ⟨key M J hJ, fun x hx => ?_⟩
  cases M with
  | zero => exact absurd (by simp [hE, Formalism.UG.hform]) hx
  | succ M =>
    obtain ⟨a, B, J', hS⟩ := exists_stepData h hJ x hx
    borelize R
    obtain ⟨-, ⟨e, he, -⟩, hc⟩ := GlobalTheory.FrameStep.frameStep F E σ h R M J x a B J' hS
    exact isUnimodularLC_of_equiv (key M J' hS.2.2.2.2.2) e (hc e he).1 (hc e he).2

theorem unimodularOver_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨d, hd⟩ := exists_conj_ne h
  exact unimodularOver_of_forall h (AF F) fun M J hJ μ _ =>
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (conj_invol h) (sub_ne_zero.2 hd)
      (by rw [map_sub, conj_invol h, neg_sub]) hJ μ

end GlobalTheory.AdelicStabUnimod
