import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValuesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverComp

theorem forms_mul_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  intro D T hL j hj σ hσ C hU N hN hMN hW w hw1 hw2 hw3 a n
  obtain ⟨hlev, hA, hinc, hUnf, hdom, hr, g, e, F, ik, φ, th, hmod, hth, hdict⟩ := hU
  have hpq := (GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨hio, -⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj σ hσ (T.V j σ) rfl hr
  have hgood : GoodEmb C.d.c₂ C.σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  have hMN' : C.d.l₂.M' ∣ N := by
    simpa [Level.M', hA] using hMN
  have key := GlobalTheory.T.coverSections_mul_stable_weberValues D T.Q hL.pins j hj C.d.l₂ C.d.Xo₂ C.d.c₂ C.σ₂ (T.V j σ) D.R.r hr C.U₂ C.dict₂
    (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) g e F ik φ th (T.x₀ j σ) hio hpos hA hgood hmod hdict hdom
    hUnf N hN hMN' hW w hw1 hw2 hw3 a n
  have hrd : ∀ f f' : Rul C.d.Xo₂ C.d.c₂,
      (∀ h, rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2 = C.σ₂ (w h) * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2) →
      C.rd a f' = fun h => C.σ₂ (w h) * C.rd a f h := by
    intro f f' hff
    funext h
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul]
    change _ * (_ * rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2) = _ * (_ * (_ * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2))
    rw [hff h]
    ring
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, ⟨hf, hc⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, -⟩ := key f hf
    exact ⟨f', ⟨hf', h2 _ hc⟩, hrd f f' h1⟩
  · rintro S hS _ ⟨f, ⟨⟨hf, hc⟩, hv⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, h3⟩ := key f hf
    exact ⟨f', ⟨⟨hf', h2 _ hc⟩, fun la hla v hvv => h3 la (hS la hla) (hv la hla) v hvv⟩, hrd f f' h1⟩

end GlobalTheory.CoverComp
