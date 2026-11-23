import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftModel

theorem isSelfDualC_lineLat : ∀ (D : D7) (S : HSp D) (ζ : Fin S.rank → D.host.E), IsLineVec S ζ → ∀ (𝔄 : FI D), (∀ d : D.host.E, d ∈ 𝔄 ↔ ∀ c ∈ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ)) → IsSelfDualC S (GlobalTheory.SeeSaw.LiftModel.lineLat S ζ 𝔄) := by
  intro D S ζ hζ 𝔄 h𝔄
  classical
  obtain ⟨h1, hH⟩ := hζ
  haveI : Subsingleton (Fin S.rank) := by rw [h1]; infer_instance
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  have all : ∀ i : Fin S.rank, i = i₀ := fun i => Subsingleton.elim _ _
  set z := ζ i₀ with hz
  set g := S.gram i₀ i₀ with hg
  have eH : star ζ ⬝ᵥ S.gram *ᵥ ζ = star z * (g * z) := by
    simp only [dotProduct, mulVec, Fintype.sum_subsingleton _ i₀, Pi.star_apply]
    rfl
  have z0 : z ≠ 0 := by
    intro h0; apply hH; rw [eH, h0]; simp
  have repr : ∀ y : Fin S.rank → D.host.E, y = (y i₀ / z) • ζ := by
    intro y; funext i; rw [all i]; simp [div_mul_cancel₀ _ z0, ← hz]
  have memΛ : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ ∃ c ∈ 𝔄, c • ζ = y := by
    intro y
    simp [lineLat, Submodule.mem_map, LinearMap.toSpanSingleton_apply]
  have memΛ' : ∀ y, y ∈ lineLat S ζ 𝔄 ↔ y i₀ / z ∈ 𝔄 := by
    intro y
    rw [memΛ]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [← hz, mul_div_cancel_right₀ _ z0] using hc
    · intro h
      exact ⟨_, h, (repr y).symm⟩
  have sum_eq : ∀ c d : D.host.E, ∑ i, ∑ j, star ((c • ζ) i) * S.gram i j * (d • ζ) j =
      star c * d * (star ζ ⬝ᵥ S.gram *ᵥ ζ) := by
    intro c d
    rw [eH]
    simp only [Fintype.sum_subsingleton _ i₀, Pi.smul_apply, smul_eq_mul, star_mul', ← hz, ← hg]
    ring
  have dual : ∀ y : Fin S.rank → D.host.E, y ∈ lineLat S ζ 𝔄 ↔
      ∀ x ∈ lineLat S ζ 𝔄, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ i, ∑ j, star (x i) * S.gram i j * y j := by
    intro y
    rw [memΛ', h𝔄]
    constructor
    · intro h x hx
      obtain ⟨c, hc, rfl⟩ := (memΛ x).1 hx
      obtain ⟨b, hb⟩ := h c hc
      refine ⟨b, ?_⟩
      conv_rhs => rw [repr y]
      rw [sum_eq, hb]
    · intro h c hc
      obtain ⟨b, hb⟩ := h (c • ζ) ((memΛ _).2 ⟨c, hc, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb]
      conv_lhs => rw [repr y]
      rw [sum_eq]
  refine ⟨⟨?_, ?_⟩, dual⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔄).map _
  · obtain ⟨c, hc, hc0⟩ : ∃ c ∈ 𝔄, c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1m : (1 : D.host.E) ∈ 𝔄 := by
        rw [h𝔄]
        intro c hc
        exact ⟨0, by simp [hcon c hc]⟩
      exact one_ne_zero (hcon 1 h1m)
    have hcζ : c • ζ ∈ lineLat S ζ 𝔄 := (memΛ _).2 ⟨c, hc, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hζs : ζ ∈ Submodule.span D.host.E (lineLat S ζ 𝔄 : Set (Fin S.rank → D.host.E)) := by
      have := Submodule.smul_mem (Submodule.span D.host.E (lineLat S ζ 𝔄 : Set (Fin S.rank → D.host.E)))
        c⁻¹ (Submodule.subset_span hcζ)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    rw [repr y]
    exact Submodule.smul_mem _ _ hζs

end GlobalTheory.SeeSaw.LiftModel
