import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.ChartGeneric

theorem not_mem_of_comap_eq_bot : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → Cn P.D.toPre.X m γ → InCone P.D.toPre γ → (∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φ.evalZ be) → ∀ h : R, h ≠ 0 → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (g : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → ∃ n : ℕ, (n : ℤ) = ℓ be ∧ Associated (g h) (ϖ ^ n)) → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (Scheme.stalkClosedPointTo ξ).hom = ⊥ → h ∉ Q := by
  intro E _ _ _ H D l Xo c Z Cn φ _ _ R _ _ _ ξ t m P k γ ℓ hCN _ _ hT _ _ _ h _ hW Q _ _ hQ0
  obtain ⟨hN, hI, hCpl, hZ⟩ := hCN
  haveI := hZ

  let xQ : Sp R := (⟨Q, inferInstance⟩ : PrimeSpectrum R)
  let x := ξ (closedPoint R)
  let p0 : Sp (Z.X.presheaf.stalk x) := Spec.map (Scheme.stalkClosedPointTo ξ) xQ
  have hp0 : (p0 : PrimeSpectrum (Z.X.presheaf.stalk x)).asIdeal = ⊥ := hQ0
  have hξ : ξ xQ = Z.X.fromSpecStalk x p0 := by
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    rfl
  have hgen : GlobalTheory.FrameCmp.GenPt (Z.X.fromSpecStalk x p0) := by
    intro q hq
    have h1 : Z.X.fromSpecStalk x p0 ⤳ x := by
      have : Z.X.fromSpecStalk x p0 ∈ Set.range (Z.X.fromSpecStalk x) := ⟨p0, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : q ∈ Set.range (Z.X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]; exact hq.trans h1
    obtain ⟨p, rfl⟩ := h2
    have hemb := (Z.X.fromSpecStalk x).isEmbedding
    have hs : p ⤳ p0 := hemb.isInducing.specializes_iff.1 hq
    have hle := (PrimeSpectrum.le_iff_specializes (R := Z.X.presheaf.stalk x) p p0).2 hs
    have : p = p0 := PrimeSpectrum.ext (le_antisymm hle (hp0 ▸ bot_le))
    rw [this]
  have habZ : ξ xQ ∈ abLocus Z.t.G := by
    obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1
    obtain ⟨u, hu⟩ := (GlobalTheory.densePart_basic Z.X _ Z.j h₁ h₂ h₃ h₄).1 (hξ ▸ hgen.mem_genericPoints)
    have : Z.jQ u ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G := by
      rw [Z.ab_gen]; exact ⟨u, rfl⟩
    rw [← hu]
    exact this
  have hab : xQ ∈ abLocus t.G := (abLocus_pullback abLocusOne Z.t.semi m.cart.1 xQ).1 habZ

  have hadm := GlobalTheory.isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hN hI hCpl
  have hop : IsOpen (abLocus t.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi
  have hL := GlobalTheory.allSixLaws
  have hU : ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1 E H R _ hadm t P hT hop
  have hco : ∀ y, ∃ r, PsiCoord P.D.toPre y r ∧ r ∉ Q := fun y => by
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main R P.D hI y).1
    exact ⟨r, hr, GlobalTheory.PsiCoordLocal.not_mem_of_coord (𝔭 := xQ) hop hab (hU y) hr⟩

  let K := FractionRing (R ⧸ Q)
  let f : R →+* K := (algebraMap (R ⧸ Q) K).comp (Ideal.Quotient.mk Q)
  have hf : ∀ r, f r = 0 ↔ r ∈ Q := fun r => by
    simp only [f, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective (f.comp (Scheme.stalkClosedPointTo ξ).hom) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Q.comap (Scheme.stalkClosedPointTo ξ).hom := (hf _).1 ha
    rw [hQ0] at this
    exact this
  haveI : CharZero (Z.X.presheaf.stalk x) := (Scheme.stalkClosedPointTo ξ).hom.charZero
  haveI : CharZero K := charZero_of_injective_ringHom hinj
  let g : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp f
  have hW' := hW (PowerSeries K) (GlobalTheory.FrameCmp.cDvr_powerSeries K) PowerSeries.X PowerSeries.X_prime.irreducible g 0
    (fun _ _ => rfl) (fun y => by
      obtain ⟨r, hr, hrQ⟩ := hco y
      refine ⟨r, 0, hr, by simp, ?_⟩
      rw [pow_zero]
      refine associated_one_iff_isUnit.2 ((Ne.isUnit ?_).map (PowerSeries.C (R := K)))
      exact fun h0 => hrQ ((hf r).1 h0))
  obtain ⟨n, hn, hass⟩ := hW'
  intro hQ
  have hn0 : n = 0 := by rw [map_zero] at hn; exact_mod_cast hn
  subst hn0
  rw [pow_zero] at hass
  have : g h = 0 := by simp only [g, RingHom.comp_apply, (hf h).2 hQ, map_zero]
  rw [this] at hass
  exact zero_ne_one (associated_zero_iff_eq_zero 1 |>.1 hass.symm).symm

end GlobalTheory.ChartGeneric
