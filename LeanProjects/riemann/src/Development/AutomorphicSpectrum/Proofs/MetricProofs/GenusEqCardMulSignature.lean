import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim

theorem ringHom_injective {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun f : E →+* ℂ => f.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro f f' h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨IsFractionRing.lift (ringHom_injective s), ?_⟩
    ext a
    simp

theorem natCard_ringHom (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card]
  exact NumberField.Embeddings.card E ℂ

def both {E Ψ : Type} [Field E] [NumberField E] (σ : Ψ → (𝓞 E →+* ℂ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ) :=
  Sum.elim σ fun τ => (starRingEnd ℂ).comp (σ τ)

theorem conj_conj_comp {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem both_bijective {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Function.Bijective (both σ) := by
  have hconj : Function.Injective fun s : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp s := by
    intro s t hst
    have := congrArg (fun u : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp u) hst
    simpa only [conj_conj_comp] using this
  have hcross : ∀ τ τ', σ τ ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' e
    exact ((h.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, e⟩
  constructor
  · rintro (τ | τ) (τ' | τ') e
    · exact congrArg Sum.inl (h.1 e)
    · exact absurd e (hcross τ τ')
    · exact absurd e.symm (hcross τ' τ)
    · exact congrArg Sum.inr (h.1 (hconj e))
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have h' : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hn
        exact hs ((h.2 s).2 hn)
      obtain ⟨τ, e⟩ := h'
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (σ τ) = s
      rw [e, conj_conj_comp]

theorem card_sum_eq_finrank {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
  rw [← natCard_ringHom E, ← Nat.card_congr (Equiv.ofBijective _ (both_bijective h)), Nat.card_eq_fintype_card]

theorem eigSp_le_eigenspace {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) (θ : 𝓞 E) :
    eigSp B s ≤ Module.End.eigenspace (B θ) (s θ) := by
  intro x hx
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx θ

theorem iSupIndep_eigSp {E V ι : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (σ : ι → (𝓞 E →+* ℂ)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp B (σ s) := by
  obtain ⟨θ, m, -, -, -, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* ℂ) (P : Polynomial ℤ), τ (Polynomial.aeval θ P) = Polynomial.aeval (τ θ) P := fun τ P =>
    (Polynomial.aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  exact ((Module.End.eigenspaces_iSupIndep (B θ)).comp hinj).mono fun s => eigSp_le_eigenspace B (σ s) θ

theorem dim_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  intro E _ _ _ Ψ _ g j j' B σ hσ hdim
  classical
  have hb := both_bijective hσ
  have htop := iSup_eigSp_eq_top B (both σ) hb.1 (card_sum_eq_finrank hσ)
  have hind := iSupIndep_eigSp B (both σ) hb.1
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun s => eigSp B (both σ s)) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun, Fintype.sum_sum_type] at e
  have h1 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inl τ))) = j' := fun τ => (hdim τ).1
  have h2 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inr τ))) = j := fun τ => (hdim τ).2
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e
  rw [← e]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim
