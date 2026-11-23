import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentSiegelSetIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryIffGroupPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.UnipSpMass

theorem exists_haar_unipSp_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      ∃ (ν : Measure (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) (𝓕 : Set (GlobalTheory.ThKLiftCusp.unipSp σ W Y)), ν.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) 𝓕 ν ∧ ν 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ hcm B d r s W hW j Y _ hY hiso
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ : IsHermND σ (c • W.J.map σ) := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B d W r s hW c hc hcs
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • W.J.map σ) Y := by
    refine ⟨Matrix.mulVec_injective_iff.1 hY, ?_⟩
    ext k l
    have h := congrArg (fun x => c * σ x) (hiso k l)
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, mul_zero] at h
    rw [Matrix.zero_apply, ← h]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply, Finset.sum_mul, Finset.mul_sum, RingHom.coe_coe]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  have hmem := GlobalTheory.UnipMatch.mem_unipSp_iff F E σ hσ B d W r s hW c hc j Y hiso
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ d W.J c hc
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc with he
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y) :=
    GlobalTheory.UAut.locallyCompact_unipRad hcm hJ hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hJ hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : GlobalTheory.ThKLiftCusp.unipSp σ W Y ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace (GlobalTheory.ThKLiftCusp.unipSp σ W Y) := eH.isClosedEmbedding.locallyCompactSpace
  haveI := GlobalTheory.UnipMass.countable_ratU' σ W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ d W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  refine GlobalTheory.T.cocompact_lattice_unit_covolume _ _ (eH ⁻¹' K') (eH.isCompact_preimage.2 hK') fun g => ?_
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    show e.symm (γ' : _) ∈ ratU σ W.J
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

end GlobalTheory.UnipSpMass
