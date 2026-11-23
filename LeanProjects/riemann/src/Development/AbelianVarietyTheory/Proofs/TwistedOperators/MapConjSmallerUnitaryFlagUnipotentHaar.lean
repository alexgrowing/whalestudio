import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapMulMtEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagModulus

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem wittHyperbolic_conj_smallerGroup_coords (d : HypDec S S₀ ρ) (h : GA D S₀) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank)
    (c : skewA D ρ) : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) * (d.emb0 h)⁻¹ =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) := by
  simp only [mul_assoc]
  rw [← mul_assoc (d.emb0 h) (d.levi u), d.wittHyperbolic_anisotropic_commute_levi h u, mul_assoc, ← mul_assoc (d.emb0 h) (d.nB b),
    d.wittHyperbolic_anisotropic_conj_nB b h, mul_assoc, ← mul_assoc (d.emb0 h) (d.nC c), d.wittHyperbolic_anisotropic_commute_nC c h, mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_conj_smallerUnitary_flagUnipotent_haar : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ν : Measure (flagN d)),
    ν.IsHaarMeasure → ∀ h : GA D S₀,
      ν.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν.map Subtype.val := by
  intro D S S₀ ρ d ν hν h
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  obtain ⟨hlc, hsc, -, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  obtain ⟨μ, lB, lC, hμ, hB, hC, sμ, sB, sC, hΦ, ν₀, hν₀, hmap⟩ := GlobalTheory.HaarCoords.haar_coords D S S₀ ρ d
  have hk : ν = Measure.haarScalarFactor ν ν₀ • ν₀ := Measure.isMulLeftInvariant_eq_smul ν ν₀
  have hconj : Measurable (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hval : Measurable (Subtype.val : flagN d → GA D S) := measurable_subtype_coe
  have hf : Measurable (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hT : Measurable (Prod.map (id : UX D ρ → UX D ρ)
      (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ))) :=
    measurable_id.prodMap (hf.prodMap measurable_id)
  have key : ν₀.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν₀.map Subtype.val := by
    have e1 : (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) =
        (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘ Subtype.val := rfl
    rw [e1, ← Measure.map_map hconj hval, hmap, Measure.map_map hconj hΦ]
    have e2 : (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∘
          Prod.map (id : UX D ρ → UX D ρ)
            (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ)) :=
      funext fun p => wittHyperbolic_conj_smallerGroup_coords d h p.1.1 p.2.1 p.2.2
    rw [e2, ← Measure.map_map hΦ hT]
    congr 1
    rw [← Measure.map_prod_map _ _ measurable_id (hf.prodMap measurable_id), ← Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id, Measure.map_id, GlobalTheory.AdelicModulus.RowMat.map_mul_mt_eq D S₀ ρ lB hB h⁻¹]
  rw [hk, Measure.map_smul, Measure.map_smul, key]

end GlobalTheory.FlagModulus

end
