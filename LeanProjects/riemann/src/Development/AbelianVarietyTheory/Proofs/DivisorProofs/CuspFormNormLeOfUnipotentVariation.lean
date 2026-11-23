import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGLStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.CuspRep

theorem norm_le_of_unip_variation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a),
    IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ),
      (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  intro E _ _ _ a ψ hψ s hs0 hsa g e he
  letI : MeasurableSpace (BlockIx a s → Ad E) := borel _
  haveI : BorelSpace (BlockIx a s → Ad E) := ⟨rfl⟩
  set μ : Measure (BlockIx a s → Ad E) := Measure.addHaar with hμ
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL E a s μ
  have hc := ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  have hI := CuspidalL2GL.integrableOn_unip hc hψ.1.left μ h𝓕 g
  have hz : ∫ x in 𝓕, ψ.1 (unip x * g) ∂μ = 0 := hψ.2 s hs0 hsa μ 𝓕 inferInstance h𝓕 g
  have key : ∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ = μ.real 𝓕 • ψ.1 g := by
    have h1 : IntegrableOn (fun _ => ψ.1 g) 𝓕 μ := integrableOn_const htop.ne
    rw [integral_sub h1 hI, hz, setIntegral_const, sub_zero]
  have hb : ‖∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ‖ ≤ e * μ.real 𝓕 :=
    norm_setIntegral_le_of_norm_le_const htop fun x _ => by rw [norm_sub_rev]; exact he x
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, mul_comm] at hb
  have hpos : 0 < μ.real 𝓕 := ENNReal.toReal_pos h0 htop.ne
  exact le_of_mul_le_mul_right hb hpos

end GlobalTheory.CuspRep
