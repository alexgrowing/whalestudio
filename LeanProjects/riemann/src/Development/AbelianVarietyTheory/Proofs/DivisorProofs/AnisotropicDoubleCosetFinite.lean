import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualThetaConvergenceAnisotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DefDcoset

open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cocompact_of_aniso (hP : GlobalTheory.Published.SiegelSetUnitary) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • J.map σ)) (han : ∀ x, form σ J x x = 0 → x = 0) :
    ∃ C : Set (UA σ J), IsCompact C ∧ ∀ h : UA σ J, ∃ γ ∈ ratU σ J, ∃ s ∈ C, h = γ * s := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ (c • J.map σ) (0 : Matrix (Fin n) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => han z (by
      have e : hE σ (c • J.map σ) z z = c * hE σ (J.map σ) z z := by
        simp only [hE, Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e] at hz
      rw [GlobalTheory.ThK.AnConv.form_eq hσ, (mul_eq_zero.1 hz).resolve_left hc, map_zero])⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient hP hcm hJ hW
  let e : UA σ J ≃* GAd σ (c • J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc)
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  refine ⟨e.symm '' C, hC.image he', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, hgs⟩ := hcov (e g)
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine ⟨e.symm γ, Subgroup.mem_subgroupOf.2 ⟨u, hu⟩, e.symm s, ⟨s, hs, rfl⟩, ?_⟩
  rw [← map_mul, ← hgs, MulEquiv.symm_apply_apply]

end GlobalTheory.ThK.DefDcoset

end
