import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRingUnitsInvertPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelConjugateEmbeddingStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.BdryGeo

theorem unit_of_vV (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  have hunit : ∀ z : T.V, (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 →
      IsUnit z := fun z hz => by
    have hzn := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by rw [hz]; exact h1)
    exact ⟨u, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by
      rw [hz, map_inv₀]
      change (valV T.V x)⁻¹ = 1
      rw [h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem descend (T₀ T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr)
    (hiF : ∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) (hi : Function.Injective i)
    (hil : IsLocalHom i) (v : T₀.Fr) (u : T.Vˣ) (hv : iF v = algebraMap T.V T.Fr (u : T.V)) :
    ∃ w : T₀.Vˣ, algebraMap T₀.V T₀.Fr w = v := by
  have hinjT : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  rcases ValuationRing.isInteger_or_isInteger T₀.V v with ⟨z, hz⟩ | ⟨z, hz⟩
  · have h1 : i z = u := hinjT (by rw [hiF, hz, hv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ u.isUnit)
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, hz⟩
  · have h1 : i z = ((u⁻¹ : T.Vˣ) : T.V) := hinjT (by rw [hiF, hz, map_inv₀, hv, map_units_inv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ (u⁻¹).isUnit)
    obtain ⟨w, rfl⟩ := this
    refine ⟨w⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem secVal_isUnit : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j →
    ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT ∧
      ∀ v : T.Fr, (∀ (k : Type) [Field k] (φ : T.Fr →+* k),
        SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A _)))) (φ v)) →
        ∃ w : T.Vˣ, algebraMap T.V T.Fr w = v := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ _ ξ β hξo hξβ
    hpA hgen g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 𝔭 h𝔭 _
  obtain ⟨hover, -, hpW, hpc, hXw, -, hZ, -, -⟩ := hcov
  have hβu := GlobalTheory.T.base_ring_units_invert_p E H l' c' W p hp hpW A β hpA
  haveI : CharZero A := by
    refine ⟨fun m n hmn => ?_⟩
    have hinjβ : Function.Injective β := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact (hβu a h0).ne_zero ha
    have h := hinjβ (show β m = β n by rw [map_natCast, map_natCast]; exact hmn)
    exact_mod_cast congrArg (fun t : c'.V W => ((t : c'.F) : ℂ)) h
  obtain ⟨T₀, iT, hinj, hloc⟩ := GlobalTheory.T.exists_dvr_over_height_one A 𝔭 h𝔭
  let α₀ : A →+* T₀.V := iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))
  have hα₀ : Function.Injective α₀ :=
    hinj.comp (IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors)
  have hψ : Function.Injective ((algebraMap T₀.V T₀.Fr).comp α₀) :=
    (IsFractionRing.injective T₀.V T₀.Fr).comp hα₀
  obtain ⟨yy₀, hyy₀⟩ := GlobalTheory.T.generic_fibre_point_field E H Dw l' Xo' c' W Y p hp hpW hpc A ξ (hXw hgen) T₀.Fr _ hψ
  obtain ⟨T, i, iF, hiF, hi, hil, io, y₀, hio, hpt⟩ :=
    GlobalTheory.T.integral_model_domain_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hover A ξ β hξβ hβu T₀ α₀ hα₀ yy₀ hyy₀
  refine ⟨T₀, iT, hinj, hloc, fun v hv => ?_⟩
  let α : A →+* T.V := i.comp α₀
  have hφeq : iF.comp ((algebraMap T₀.V T₀.Fr).comp (iT.comp (algebraMap A _))) = (algebraMap T.V T.Fr).comp α :=
    RingHom.ext fun a => (hiF _).symm
  let yy : Sp T.Fr ⟶ Xo'.XF c' := spMap iF ≫ yy₀
  have hyy : yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ := by
    rw [← hφeq, Category.assoc, hyy₀, sp_sp]
  have hpt' : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) := by
    rw [hpt, Category.assoc]
  obtain ⟨w₁, w₂, g₁, g₂, hc1, hc2, ⟨hc3, hc4⟩, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ :=
    GlobalTheory.T.integral_model_conjugate_embedding E H Dw l l' Xo Xo' c c' W Y r ν hle hover τ.1 A ξ β hξβ g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 T α io y₀ yy
      hyy hpt'
  letI := io.toAlgebra
  have hv' := hv T.Fr iF
  rw [hφeq] at hv'
  have key := hv' io.toAlgebra yy hyy y₀.1 y₀.2.1 hpt' w₁ w₂ g₁ g₂ hc1 hc2 hc3 hc4
  have hLies : GlobalTheory.AllWt.LiesOn Z y₀.1 := by
    intro s'
    rw [hpt']
    apply hZ
    have hs' : s' = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim _ _
    have e1 : (yy ≫ Y.j) s' ∈ Xw := by
      rw [hyy, hs', bot_map (φ := (algebraMap T.V T.Fr).comp α) ((IsFractionRing.injective T.V T.Fr).comp (hi.comp hα₀))]
      exact hgen
    exact e1
  have hn := GlobalTheory.T.archimedean_section_integral_frame hP1 hP2 hP3 E H Dw l Xo c r₀ U x hL Z τ s T io y₀ hio hLies
  have hev0 : evI y₀ s.sig ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hn
    exact EReal.top_ne_zero hn
  have hvv : vV T.V (evI y₀ s.sig) = 0 := by
    rw [nval_of_ne hev0] at hn
    have : ((vV T.V (evI y₀ s.sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    simpa using this
  obtain ⟨u₃, hu₃⟩ := unit_of_vV T hev0 hvv
  have hkey : iF v = algebraMap T.V T.Fr ((u₂ * u₃ * u₁⁻¹ : T.Vˣ) : T.V) := by
    have hne : algebraMap T.V T.Fr (u₁ : T.V) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u₁.ne_zero
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hu₂, hu₃, map_units_inv, hu₁]
    have : iF v * g₁.det = g₂.det * evI y₀ s.sig := key
    rw [← hu₁] at this ⊢
    field_simp
    linear_combination this
  exact descend T₀ T i iF hiF hi hil v _ hkey

end GlobalTheory.FlatModel.BdryGeo
