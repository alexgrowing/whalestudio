import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMovesIsotropicLineToScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorNonzeroPairingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalConjugateUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.WittLineCT

theorem transport {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ U₀ U : Subgroup G) (g₀ : G) (hg₀ : g₀ ∈ Γ) (hin : ∀ v ∈ U₀, g₀ * v * g₀⁻¹ ∈ U)
    (hout : ∀ v ∈ U, g₀⁻¹ * v * g₀ ∈ U₀) (φ : G → ℂ) (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g)
    (h : ∀ (μ : Measure U₀) (𝓕 : Set U₀), μ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf U₀) 𝓕 μ → μ 𝓕 = 1 →
      ∀ g, (0 : ℂ) = ∫ u in 𝓕, φ ((u : G) * g) ∂μ) :
    ∀ (μ : Measure U) (𝓕 : Set U), μ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf U) 𝓕 μ → μ 𝓕 = 1 →
      ∀ g, (0 : ℂ) = ∫ u in 𝓕, φ ((u : G) * g) ∂μ := by
  let e : U₀ ≃* U :=
    { toFun := fun v => ⟨g₀ * v * g₀⁻¹, hin _ v.2⟩
      invFun := fun v => ⟨g₀⁻¹ * v * g₀, hout _ v.2⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hec : Continuous e :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hes : Continuous e.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let em : U₀ ≃ᵐ U := (⟨e.toEquiv, hec, hes⟩ : U₀ ≃ₜ U).toMeasurableEquiv
  have hem : ∀ v, (em v : G) = g₀ * v * g₀⁻¹ := fun v => rfl
  have hems : ∀ v, ((e.symm v : U₀) : G) = g₀⁻¹ * v * g₀ := fun v => rfl
  intro μ 𝓕 hμ h𝓕 hm g
  let ν : Measure U₀ := μ.map em.symm
  have hmap : ν.map em = μ := by
    simp only [ν]; rw [Measure.map_map em.measurable em.symm.measurable]; simp
  have hν : ν.IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e.symm hes hec
  have hF : IsFundamentalDomain (Γ.subgroupOf U₀) (em ⁻¹' 𝓕) ν := by
    refine h𝓕.preimage_of_equiv (f := em) (hmap ▸ (em.measurable.measurePreserving ν).quasiMeasurePreserving)
      (e := fun q => ⟨e.symm q.1, show ((e.symm q.1 : U₀) : G) ∈ Γ from
        hems q.1 ▸ mul_mem (mul_mem (inv_mem hg₀) q.2) hg₀⟩) ?_ ?_
    · constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro p
        refine ⟨⟨e p.1, show ((e p.1 : U) : G) ∈ Γ from
          (show ((e p.1 : U) : G) = g₀ * p.1 * g₀⁻¹ from rfl) ▸ mul_mem (mul_mem hg₀ p.2) (inv_mem hg₀)⟩, ?_⟩
        exact Subtype.ext (e.symm_apply_apply p.1)
    · intro q v
      apply Subtype.ext
      change g₀ * ((g₀⁻¹ * (q.1 : G) * g₀) * v) * g₀⁻¹ = (q.1 : G) * (g₀ * v * g₀⁻¹)
      group
  have h1' : ν (em ⁻¹' 𝓕) = 1 := by
    rw [← hm, ← hmap, em.map_apply]
  have key := h ν (em ⁻¹' 𝓕) hν hF h1' (g₀⁻¹ * g)
  have hpt : ∀ v : U₀, φ ((em v : G) * g) = φ ((v : G) * (g₀⁻¹ * g)) := fun v => by
    simp only [hem, mul_assoc]; exact hφ g₀ hg₀ _
  rw [← hmap, setIntegral_map_equiv]
  simp only [hpt]
  exact key

theorem isConstTerm_zero_of_isConstTerm_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) →
      ∀ x₀ x : Matrix (Fin n) (Fin 1) E, x₀ ≠ 0 → Formalism.UG.cT (σ : E →+* E) x₀ * J * x₀ = 0 → x ≠ 0 →
        Formalism.UG.cT (σ : E →+* E) x * J * x = 0 → IsConstTerm σ J x₀ φ 0 → IsConstTerm σ J x φ 0 := by
  intro F E _ _ _ _ _ σ hσ n J hJ φ hφ x₀ x hx₀ h0 hx h1 hct
  obtain ⟨γ, c, hc, hγ⟩ : ∃ (γ : GRat σ J) (c : E), c ≠ 0 ∧ (γ.1 : Matrix (Fin n) (Fin n) E) * x₀ = c • x := by
    by_cases ha : Formalism.UG.cT (σ : E →+* E) x₀ * J * x = 0
    · obtain ⟨u, hu, hu0, hux⟩ := GlobalTheory.T.exists_isotropic_vector_pairing_ne_zero F E σ hσ n J hJ x₀ x hx₀ hx h0 ha
      obtain ⟨γ₁, hγ₁, c₁, hc₁, e₁⟩ := GlobalTheory.T.unitary_moves_isotropic_line_to_scalar F E σ hσ n J hJ x₀ u h0 hu hu0
      obtain ⟨γ₂, hγ₂, c₂, hc₂, e₂⟩ := GlobalTheory.T.unitary_moves_isotropic_line_to_scalar F E σ hσ n J hJ u x hu h1 hux
      refine ⟨⟨γ₂ * γ₁, mul_mem hγ₂ hγ₁⟩, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
      simp only [Units.val_mul, Matrix.mul_assoc, e₁, Matrix.mul_smul, e₂, smul_smul, mul_comm c₁ c₂]
    · obtain ⟨γ, hγ, c, hc, e⟩ := GlobalTheory.T.unitary_moves_isotropic_line_to_scalar F E σ hσ n J hJ x₀ x h0 h1 ha
      exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  set g₀ := ratEmb σ J γ with hg₀
  have hin : ∀ v ∈ unipRad σ J x₀, g₀ * v * g₀⁻¹ ∈ unipRad σ J x :=
    GlobalTheory.T.rational_conjugate_unipotent_radical F E σ n 1 J γ x₀ x (c • 1) (c⁻¹ • 1) (by simp [smul_smul, hc]) (by simp [smul_smul, hc])
      (by rw [hγ, Matrix.mul_smul, Matrix.mul_one])
  have hout : ∀ v ∈ unipRad σ J x, g₀⁻¹ * v * g₀ ∈ unipRad σ J x₀ := by
    intro v hv
    have := GlobalTheory.T.rational_conjugate_unipotent_radical F E σ n 1 J γ⁻¹ x x₀ (c⁻¹ • 1) (c • 1) (by simp [smul_smul, hc]) (by simp [smul_smul, hc]) (by
      have e1 : ((γ⁻¹).1 : Matrix (Fin n) (Fin n) E) * (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [Matrix.mul_smul, Matrix.mul_one]
      have := congrArg (fun M => c⁻¹ • (((γ⁻¹).1 : Matrix (Fin n) (Fin n) E) * M)) hγ
      simp only [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← Matrix.mul_assoc, e1, Matrix.one_mul] at this
      exact this.symm) v hv
    simpa [g₀, map_inv] using this

  have hg₀ : g₀ ∈ ratPts σ J := range_ratEmb σ J ▸ ⟨γ, rfl⟩
  intro μ 𝓕 hμ h𝓕 hm g
  have := transport (ratPts σ J) (unipRad σ J x₀) (unipRad σ J x) g₀ hg₀ hin hout φ hφ
    (fun μ 𝓕 hμ h𝓕 hm g => by simpa using hct μ 𝓕 hμ h𝓕 hm g) μ 𝓕 hμ h𝓕 hm g
  simpa using this

end GlobalTheory.WittLineCT

end
