import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem stdGap_of_gapLap {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    StdGap ε lam := by
  obtain ⟨hA, hG, hN⟩ := hg
  refine ⟨hA, h, hG, ?_⟩
  have h1 : (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤
      max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) := le_max_right _ _
  have h2 : 2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := by
    unfold hNeed
    exact le_max_left _ _
  linarith

theorem exists_isMu {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) : ∃ μ : Fin n → ℤ, S7.IsMu lam μ := by
  obtain ⟨_, hm⟩ := hlam
  choose m hm using hm
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), ?_⟩
  intro a
  have ha := hm a
  simp only [ReciprocityTheory.ChartRestriction.DS.rho]
  push_cast
  linarith

theorem datum_link (hPD : PsiDatumStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hlam : S7.IsHCParam lam) (hg : GapLap ε lam h) (hq : 1 ≤ S7.q0 ε)
    (T : S7.KType ε (lowK ε lam)) {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ) :
    ∃ ι : V ≃ₗ[ℂ] T.V,
      (∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) ∧
      (∀ v v' : V, ⟪ι v', ι v⟫_ℂ = ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ) ∧
      ∀ (k : S7.KG ε) (v w : V), ((w : D) : H) = σ (S7.toMK k) ((v : D) : H) →
        ι w = T.op k (ι v) := by
  obtain ⟨H₂, _, _, _, σ₂, D₂, E₂, V₂, ι₂, hσ₂, hD₂, hV₂, hc₂, hVK₂, hco⟩ :=
    hPD n ε lam h T μ hlam hg.2.1 hg.2.2 hq hμ
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hV hσ₂ hD₂ hV₂
  obtain ⟨ψ, -, hψI⟩ := KTypeIsomorphism.exists_phi hσ₂ hD₂ hV₂ hσ hD hV
  have := hV.1
  have := hV₂.1
  have hφi : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun v hv => by
    have h1 := hφI v v
    rw [hv] at h1
    simpa using h1.symm
  have hψi : Function.Injective ψ := (injective_iff_map_eq_zero ψ).mpr fun v hv => by
    have h1 := hψI v v
    rw [hv] at h1
    simpa using h1.symm
  have hrk : Module.finrank ℂ V = Module.finrank ℂ V₂ :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hφi)
      (LinearMap.finrank_le_finrank_of_injective hψi)
  let e : V ≃ₗ[ℂ] V₂ := φ.linearEquivOfInjective hφi hrk
  have hU := rigid_universal hσ hD hV hc hVK hσ₂ hD₂ hV₂ hc₂ hVK₂ (stdGap_of_gapLap hg) φ hφK hφI
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hcoef : ∀ g ∈ UJset ε, ∀ v v' : V, ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ =
      ⟪(e.trans ι₂) v', S7.PsiM T μ g ((e.trans ι₂) v)⟫_ℂ := fun g hgm v v' => by
    rw [← hU g hgm v v', hco g hgm]; rfl
  have hiso : ∀ v v' : V, ⟪(e.trans ι₂) v', (e.trans ι₂) v⟫_ℂ =
      ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ := fun v v' => by
    have := hcoef 1 h1J v v'
    rw [hσ.1.1, S7.psiM_one] at this
    exact this.symm
  refine ⟨e.trans ι₂, hcoef, hiso, fun k v w hw => ?_⟩
  have hk : S7.PsiM T μ (S7.toMK k) = T.op k := by
    have := S7.psiM_equiv T μ k 1 (g := 1) h1J
    rwa [S7.toMK_one', Matrix.mul_one, Matrix.mul_one, S7.psiM_one, S7.op_one', mul_one, mul_one] at this
  refine ext_inner_left ℂ fun x => ?_
  obtain ⟨v', rfl⟩ := (e.trans ι₂).surjective x
  rw [hiso, hw, hcoef _ k.1.2, hk]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
