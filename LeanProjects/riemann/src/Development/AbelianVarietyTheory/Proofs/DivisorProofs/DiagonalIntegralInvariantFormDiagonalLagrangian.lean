import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagLagrNorm
open MeasureTheory GlobalTheory.DiagForm IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem map_eI_eq : ∃ k : NNReal, k ≠ 0 ∧
    Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) := by
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  have : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  have : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have : (Measure.map (eI F κ) (volume : Measure (Vi F κ))).IsAddHaarMeasure :=
    (eI F κ).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem integral_compD {k : NNReal}
    (hk : Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)))
    (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) =
      (k : ℂ) * ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  rw [SchwartzMap.integralCLM_apply]
  have e : ∀ u, compD F κ f u = (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x)) (eI F κ u) :=
    fun u => rfl
  simp only [e]
  have h1 := integral_map_equiv (μ := (volume : Measure (Vi F κ))) (eI F κ).toHomeomorph.toMeasurableEquiv
    (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x))
  change ∫ y, f (Sum.elim y y) ∂(Measure.map (eI F κ) volume) = ∫ x, f (Sum.elim (eI F κ x) (eI F κ x)) at h1
  rw [hk, integral_smul_nnreal_measure] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]

theorem exists_SB_ne : ∃ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
    (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  refine ⟨g, hg, ?_⟩
  rw [hgV, integral_indicator_const _ hVo.measurableSet]
  have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
  have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
  have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
  simpa using this.ne'

end GlobalTheory.DiagLagrNorm

namespace GlobalTheory.RealLift

open MeasureTheory GlobalTheory.DiagForm GlobalTheory.DiagLagrNorm

theorem diagLagr_invForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd _ hdd
  obtain ⟨k, hk0, hk⟩ := map_eI_eq (F := F) (κ := κ)
  obtain ⟨g, hg, hc⟩ := exists_SB_ne (F := F) (κ := κ)
  set c : ℂ := (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) * (k : ℂ) with hcdef
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hc0 : c ≠ 0 := mul_ne_zero hc hk'
  refine ⟨c⁻¹ • lDiag F κ, ?_, ?_, g, hg, ?_⟩
  · intro g' hg'
    obtain ⟨T, hT⟩ := lDiag_adm (F := F) (κ := κ) g' hg'
    exact ⟨c⁻¹ • T, fun f => by simp [hT f]⟩
  · intro z φ hφ
    have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    have hr : dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ =
        schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) φ := by
      rw [hz, Darboux.rho, hdd z z]
    simp only [LinearMap.smul_apply]
    rw [hr, lDiag_schr ψ _ _ hφ]
  · intro f
    simp only [LinearMap.smul_apply]
    rw [lDiag_pureA f hg, integral_compD hk, smul_eq_mul, hcdef]
    field_simp

end GlobalTheory.RealLift
