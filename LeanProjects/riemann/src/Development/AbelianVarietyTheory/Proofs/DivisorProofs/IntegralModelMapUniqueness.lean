import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapFlatExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitOfDvrUnitStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flatSec_unit_at_bdry_height_one : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr
  haveI hN : IsNoetherianRing A := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  let P0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hbotR : ξ P0 ∈ Set.range Y.j := hcov.2.2.2.2.1 hbot
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.integral_model_map_extension hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ P0 hbotR
  obtain ⟨T, iT, hiT, hloc, hval⟩ := GlobalTheory.T.section_value_unit_at_boundary_height_one_prime hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr

  set gT : A →+* T.Fr := (algebraMap T.V T.Fr).comp (iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) with hgT
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  have hgTinj : Function.Injective gT :=
    (IsFractionRing.injective T.V T.Fr).comp (hiT.comp hAinj)
  have hunits : ∀ b : P0.asIdeal.primeCompl, IsUnit (gT b) := fun b =>
    isUnit_iff_ne_zero.2 fun h => b.2 (by
      have : (b : A) = 0 := hgTinj (by rw [h, map_zero])
      simp [P0, this])
  let κ : Localization.AtPrime P0.asIdeal →+* T.Fr := IsLocalization.lift hunits
  have hκ : κ.comp (algebraMap A _) = gT := IsLocalization.lift_comp hunits
  obtain ⟨w, hw⟩ := hval (κ u₀) fun k _ φ => by
    have h0 := hu₀ k (φ.comp κ)
    rwa [RingHom.comp_assoc, hκ] at h0
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective P0.asIdeal.primeCompl (u₀ : Localization.AtPrime P0.asIdeal)
  have h1 : gT a = gT b * algebraMap T.V T.Fr w :=
    (IsLocalization.lift_mk'_spec _ _ _ _).1 (by simp only at hab; rw [hab, hw])
  have h2 : iT (algebraMap A _ a) = iT (algebraMap A _ b) * w := by
    apply IsFractionRing.injective T.V T.Fr
    simpa [hgT, map_mul] using h1
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_local_unit_of_dvr_unit A 𝔭 hht T.V iT hiT hloc a b ⟨w, h2⟩
  refine ⟨u, fun k _ φ => ?_⟩
  set ψ : A →+* k := φ.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) with hψ
  by_cases hk : Function.Injective ψ
  ·
    have hunits' : ∀ b : P0.asIdeal.primeCompl, IsUnit (ψ b) := fun b =>
      isUnit_iff_ne_zero.2 fun h => b.2 (by
        have : (b : A) = 0 := hk (by rw [h, map_zero])
        simp [P0, this])
    let φ' : Localization.AtPrime P0.asIdeal →+* k := IsLocalization.lift hunits'
    have hφ' : φ'.comp (algebraMap A _) = ψ := IsLocalization.lift_comp hunits'
    have hle' : 𝔭.asIdeal.primeCompl ≤ P0.asIdeal.primeCompl.comap (RingHom.id A) := fun x hx hx0 => by
      apply hx
      have : x = 0 := by simpa [P0] using hx0
      rw [this]; exact 𝔭.asIdeal.zero_mem
    let mp : Localization.AtPrime 𝔭.asIdeal →+* Localization.AtPrime P0.asIdeal :=
      IsLocalization.map _ (RingHom.id A) hle'
    have hφ : φ = φ'.comp mp := by
      apply IsLocalization.ringHom_ext 𝔭.asIdeal.primeCompl
      rw [RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_id, hφ']
    have hmu : mp u = u₀ := by
      rw [← hab, IsLocalization.eq_mk'_iff_mul_eq]
      have := congrArg mp hu
      rw [map_mul] at this
      simpa [mp, IsLocalization.map_eq] using this
    have e2 : φ u = φ' u₀ := by
      rw [← hmu]
      exact congrArg (fun f : Localization.AtPrime 𝔭.asIdeal →+* k => f u) hφ
    rw [e2, ← hφ']
    exact hu₀ k φ'
  ·
    intro _ yy hyy
    exfalso
    apply hnr
    have hker : RingHom.ker ψ = 𝔭.asIdeal := by
      have hle : RingHom.ker ψ ≤ 𝔭.asIdeal := fun x hx => by
        by_contra hx'
        have hu' : IsUnit (algebraMap A (Localization.AtPrime 𝔭.asIdeal) x) :=
          IsLocalization.map_units _ (⟨x, hx'⟩ : 𝔭.asIdeal.primeCompl)
        have := (hu'.map φ).ne_zero
        exact this hx
      have hne : RingHom.ker ψ ≠ ⊥ := fun h => hk ((RingHom.injective_iff_ker_eq_bot ψ).2 h)
      by_contra hne'
      have hlt : RingHom.ker ψ < 𝔭.asIdeal := lt_of_le_of_ne hle hne'
      have hlt0 : (⊥ : Ideal A) < RingHom.ker ψ := bot_lt_iff_ne_bot.2 hne
      have a1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt0
      have a2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, hht] at *
      rw [zero_add] at a1
      have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add a1 le_rfl).trans a2
      exact absurd this (by decide)
    have hpt : (spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) = 𝔭 := PrimeSpectrum.ext hker
    refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    calc Y.j (yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k))
        = (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap ψ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      _ = ξ ((spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) := Scheme.Hom.comp_apply _ _ _
      _ = ξ 𝔭 := by rw [hpt]

end GlobalTheory.FlatModel
