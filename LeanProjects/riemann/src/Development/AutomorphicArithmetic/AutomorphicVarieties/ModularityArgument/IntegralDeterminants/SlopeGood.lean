import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.ProdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

private theorem nu_mul {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x y : ℂ) :
    nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu, map_mul, norm_mul]

private theorem nu_inv {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : ℂ) :
    nu ι x⁻¹ = (nu ι x)⁻¹ := by
  simp [nu, map_inv₀, norm_inv]

private theorem algSat_map (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem prod_zpow_add {α : Type} (s : Finset α) (p : α → ℝ) (hp : ∀ t ∈ s, 0 < p t) (a c : α → ℤ) :
    ∏ t ∈ s, p t ^ (a t + c t) = (∏ t ∈ s, p t ^ a t) * ∏ t ∈ s, p t ^ c t := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht => zpow_add₀ (hp t ht).ne' _ _

private theorem prod_zpow_neg {α : Type} (s : Finset α) (p : α → ℝ) (a : α → ℤ) :
    ∏ t ∈ s, p t ^ (-a t) = (∏ t ∈ s, p t ^ a t)⁻¹ := by
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun t _ => zpow_neg _ _

private theorem bnd_untwist {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (hp : ∀ τ ∈ Ov ι w, 0 < nu ι (τ (unif w : E)))
    (m lo hi : (E →+* ℂ) → ℤ) (e b : ℂ)
    (he : nu ι e * ∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ m τ = 1)
    (h1 : Bnd ι w (fun τ => hi τ + m τ) (b * e))
    (h2 : Bnd ι w (fun τ => -(lo τ + m τ)) (b * e)⁻¹) :
    Bnd ι w hi b ∧ Bnd ι w (fun τ => -lo τ) b⁻¹ := by
  unfold Bnd at *
  set p : (E →+* ℂ) → ℝ := fun τ => nu ι (τ (unif w : E)) with hpdef
  set M := ∏ τ ∈ Ov ι w, p τ ^ m τ with hM
  constructor
  · rw [prod_zpow_add _ p hp hi m, nu_mul] at h1
    calc _ = nu ι b * (∏ τ ∈ Ov ι w, p τ ^ hi τ) * (nu ι e * M) := by rw [he, mul_one]
      _ = _ := by ring
      _ ≤ 1 := h1
  · have e1 : ∏ τ ∈ Ov ι w, p τ ^ (-(lo τ + m τ)) = (∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * M⁻¹ := by
      rw [prod_zpow_neg, prod_zpow_add _ p hp lo m, mul_inv, ← prod_zpow_neg]
    rw [e1] at h2
    have e2 : (nu ι e)⁻¹ * M⁻¹ = 1 := by rw [← mul_inv, he, inv_one]
    calc _ = nu ι b⁻¹ * (∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * ((nu ι e)⁻¹ * M⁻¹) := by rw [e2, mul_one]
      _ = nu ι (b * e)⁻¹ * ((∏ τ ∈ Ov ι w, p τ ^ (-lo τ)) * M⁻¹) := by
        rw [nu_inv, nu_inv, nu_mul, mul_inv]; ring
      _ ≤ 1 := h2

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.slopeGood :
    UpperTheory.V.Z.Int.SlopeOn .csd → UpperTheory.V.Z.Int.SlopeOn .good := by
  intro hC l _ ι E _ _ _ l' n hl' hn π χ hS w hw B hB lo hi hW b hb
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified GlobalTheory.automorphicFormsFiniteGL E l' n hn π χ hS w hw
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E n π κ w B hu hB
  have hinf : ∀ τ, (CG.mk (π.twist κ)).infChar τ = ((CG.mk π).infChar τ).map (· + (m τ : ℂ)) := by
    intro τ
    rw [← (GlobalTheory.CuspRep.InfType.expo_of_infType E κ).1 m hκ τ]
    exact ((GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _).twist κ).infChar_eq
  have hW' : ∀ τ, Within n ((CG.mk (π.twist κ)).infChar τ) (lo τ + m τ) (hi τ + m τ) := by
    intro τ z hz
    rw [hinf, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨k, rfl, h1, h2⟩ := hW τ y hy
    exact ⟨k + m τ, by push_cast; ring, by omega, by omega⟩
  have hb' : b * (κ.val w : ℂ) ∈ algSat n (normV w) (B.map (· * κ.val w)) := by
    rw [algSat_map] at hb ⊢
    rw [Multiset.mem_map] at hb
    obtain ⟨α, hα, rfl⟩ := hb
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨α, hα, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := hC l ι E l' n hl' hn (π.twist κ) _ hS' w hw _ hB' _ _ hW' _ hb'
  exact bnd_untwist ι w (fun τ hτ => ((prodNorm l ι E w).1 τ hτ).1) m lo hi _ b
    (charVal l ι E κ m hκ w hu) h1 h2
