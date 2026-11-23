import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMatchedPlaneTowerDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTranslateAutomorphicConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetJNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

theorem _root_.GlobalTheory.T.iso_plane_eisenstein_strip : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (χa χb : Chr F E) (za zb : ℝ), za < zb → ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ f : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAut σ (c • Y.J.map σ) K (fun x => f ((toGAd hσ Y.J hc).symm x))) →
      ∀ fa fb : UA σ Y.J → ℂ, SplitZ Y₁ P χa χb za zb f fa fb →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∀ K₁ : Subgroup (GAd σ (c • Y₁.J.map σ)), (∀ x ∈ K₁, (toGAd hσ Y₁.J hc).symm x ∈ KInf σ Y₁ B.emb) →
        IsAut σ (c • Y₁.J.map σ) K₁ (fun x => g ((toGAd hσ Y₁.J hc).symm x)) := by
  intro kp F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hsk hI χa χb za zb hz c hc hcc f hf fa fb hs h hh hex g hg K₁ hK₁
  obtain ⟨⟨t, m, hm, ht⟩, hdom, hrat⟩ := GlobalTheory.ThK.DescB.LevRatInv.plane_facts B hB hsk hI
  have h1K : (1 : UA σ Y.J) ∈ KInf σ Y B.emb := by
    exact ⟨fun u _ => by simp [mat], fun w => by simp [mat]⟩
  have hf' : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x := by
    intro γ hγ x
    have hK : ∀ x ∈ (⊥ : Subgroup (GAd σ (c • Y.J.map σ))), (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb := by
      intro x hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      simpa using h1K
    have := (hf ⊥ hK).mod.left (toGAd hσ Y.J hc γ) ((GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ Y.J hc γ).2 hγ) (toGAd hσ Y.J hc x)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using this
  set la := GlobalTheory.ThK.DescB.PrimeSplit.lawFn χa za t
  set lb := GlobalTheory.ThK.DescB.PrimeSplit.lawFn χb zb t
  have hne : la - lb ≠ 0 := sub_ne_zero.2 (GlobalTheory.ThK.DescB.PrimeSplit.lawFn_ne χa χb hz ht)
  have hform : ∀ x, fa x = (la - lb)⁻¹ * (fa + fb) (m * x) + (-(lb * (la - lb)⁻¹)) * (fa + fb) x := by
    intro x
    have ea := hs.2.1 t m hm x
    have eb := hs.2.2 t m hm x
    simp only [Pi.add_apply, ea, eb]
    change fa x = (la - lb)⁻¹ * (la * fa x + lb * fb x) + -(lb * (la - lb)⁻¹) * (fa x + fb x)
    field_simp
    ring
  have hFA : ∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
      IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x)) := by
    intro K hK
    have := GlobalTheory.T.levi_translate_automorphic_constant_term F E σ hσ n n₁ Y Y₁ P c hc t m hm (fa + fb) (la - lb)⁻¹ (-(lb * (la - lb)⁻¹)) K
      (GlobalTheory.T.isotropic_plane_constant_term_formula F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc χa χb za zb f hf fa fb hs K hK)
    convert this using 2 with x
    exact hform _
  refine ⟨⟨?_, GlobalTheory.T.isotropic_plane_constant_term_level F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg,
    GlobalTheory.T.isotropic_plane_constant_term_vanishing F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg,
    GlobalTheory.T.isotropic_plane_constant_term_equivariant F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg,
    GlobalTheory.T.isotropic_plane_constant_term_growth F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg⟩,
    GlobalTheory.T.isotropic_plane_constant_term_moderate F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg K₁ hK₁,
    GlobalTheory.LeviGenZFin.zfin kp F E σ hσ B hB n n₁ Y Y₁ P hsk hI c hc hcc fa hFA h hh hex g hg⟩
  intro γ hγ x
  have hγ' : (toGAd hσ Y₁.J hc).symm γ ∈ ratU σ Y₁.J :=
    (GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ Y₁.J hc _).1 (by simpa using hγ)
  have := GlobalTheory.ThK.DescB.LevRatInv.gen_inv hz ⟨t, m, hm, ht⟩ hdom hrat hf' hs h hex hg _ hγ' ((toGAd hσ Y₁.J hc).symm x)
  simpa only [map_mul] using this
