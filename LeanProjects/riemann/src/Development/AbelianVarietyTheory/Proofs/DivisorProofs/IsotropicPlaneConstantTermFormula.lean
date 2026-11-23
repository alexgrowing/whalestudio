import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactInvariantFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
theorem _root_.GlobalTheory.T.isotropic_plane_constant_term_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ (χa χb : Chr F E) (za zb : ℝ) (f : UA σ Y.J → ℂ),
      (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAut σ (c • Y.J.map σ) K (fun x => f ((toGAd hσ Y.J hc).symm x))) →
      ∀ fa fb : UA σ Y.J → ℂ, SplitZ Y₁ P χa χb za zb f fa fb →
      ∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => (fa + fb) ((toGAd hσ Y.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hsk hP c hc hcs χa χb za zb f hf fa fb hsplit K hK
  have hcm := hB.cm
  set C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => P.x i with hCdef
  have hd : Y.J.det ≠ 0 := GlobalTheory.IsoPlaneProj.det_ne_zero_of_cartan B Y hP.2.2.2.2.2.2.1
  have hd₁ : Y₁.J.det ≠ 0 := GlobalTheory.IsoPlaneProj.det_ne_zero_of_cartan B Y₁ hP.2.2.2.2.2.2.2.cartan
  have hJ : IsHermND σ (c • Y.J.map σ) := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hsk hd hc hcs
  have hC := GlobalTheory.UnipCocptForm.isIsoCols_smul_map_of_isotropic_pair σ Y.J P.x P.y hP.2.1 hP.2.2.2.1 hσ c
  have hA := hf K hK
  obtain ⟨cc, hcc, -⟩ := existsUnique_isConstTerm hcm hJ hC (isAut_iff_isAutOn.1 hA).left
  have haut := (GlobalTheory.UAut.ConstAut.isAutOn_constTerm F E σ hcm _ _ hJ 1 _ (fun _ => 0) hC _ K _ cc inf_le_left (isAut_iff_isAutOn.1 hA)
    (isConstTerm_iff_unipFlag.1 hcc)).1
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hB n n₁ Y Y₁ P hsk hP
  have heq : cc = fun x => (fa + fb) ((toGAd hσ Y.J hc).symm x) := by
    funext x
    have h2 := GlobalTheory.TorFinIso.setIntegral_unip_eq_constTerm_iso σ B Y Y₁ P hsk hP hσ c hc f μ 𝓕 h𝓕 h1 cc hcc
      ((toGAd hσ Y.J hc).symm x)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [← h2, hsplit.1 μ 𝓕 hμ h𝓕 h1]
  have hmem : ∀ g : UA σ Y.J, g ∈ unip σ Y P ↔ toGAd hσ Y.J hc g ∈ unipRad σ (c • Y.J.map σ) C := fun g =>
    GlobalTheory.UnipCocptForm.mem_unip_iff σ hσ Y Y₁.J P hsk hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hd₁ c hc g
  rw [heq] at haut
  refine haut.mono ?_ le_rfl
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.mem_sup_left ?_
  rw [unipFlag_const]
  exact (hmem g).1 hg
