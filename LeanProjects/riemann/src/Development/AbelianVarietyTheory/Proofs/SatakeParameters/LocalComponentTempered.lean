import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisWeightEqDimSubOneStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CsdTempered

theorem hasInfChar_of_isRegAlg {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 2 ≤ a) {π : CuspSub E a}
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) : ∃ m, π.HasInfChar τ m := by
  by_contra hn
  have hn' : ¬ ∃ m, (CG.mk π).HasInfChar τ m := hn
  have h1 := (hr τ).1
  rw [CG.infChar, dif_neg hn'] at h1
  rw [Multiset.nodup_iff_count_le_one] at h1
  have h2 := h1 0
  rw [Multiset.count_replicate_self] at h2
  omega

theorem tempered_of_prime (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 2 ≤ a) {π : CuspSub E a}
    (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (h : IsPlaceOver A w) {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).tempered := by
  have ha1 : 1 ≤ a := by omega
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha1 hr hc
  have hwt := GlobalTheory.T.galois_weight_eq_dim_sub_one E Ω l ι a ha1 π _ r wt HT (hasInfChar_of_isRegAlg ha hr) hc H
  have h1 := H.tempered_wdOf hl h
  rw [H.wdOf_eq hl hrc hσ, WD.lpTw_add, hwt,
    show (1 - (a : ℝ)) / 2 + ((((a : ℤ) - 1 : ℤ) : ℝ)) / 2 = 0 by push_cast; ring, WD.lpTw_zero] at h1
  exact h1

theorem main : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, (CG.mk π).IsRegAlg → π.IsCsd → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).tempered := by
  intro hG E Ω _ _ _ _ _ _ a ha π hr hc A w h rc hrc σ hσ
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · have h3 : ((3 : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h3 => w.isPrime.ne_top <| by
      rw [Ideal.eq_top_iff_one]
      have e : ((3 : ℕ) : 𝓞 E) - ((2 : ℕ) : 𝓞 E) = 1 := by push_cast; ring
      rw [← e]
      exact w.asIdeal.sub_mem h3 h2
    obtain ⟨ι⟩ : Nonempty (Qbar 3 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 3
    exact tempered_of_prime hG ha hr hc h hrc hσ 3 ι h3
  · obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
    exact tempered_of_prime hG ha hr hc h hrc hσ 2 ι h2

end GlobalTheory.CsdTempered
