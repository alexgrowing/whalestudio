import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToLocalRingOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelTangentOverInclusionStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModelOpen

theorem unit_loc : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
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
    ∀ 𝔭 : PrimeSpectrum A, ξ 𝔭 ∈ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw _ hcov A _ _ _ ξ β _ hβ _ hgen
    g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ 𝔭 h𝔭
  haveI := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  obtain ⟨yL, hyL⟩ := GlobalTheory.T.lift_to_local_ring_open_immersion Y.j ξ 𝔭 h𝔭
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨alg, z, w₁, w₂, hz, hc₁, hc₂, hz₁, hz₂⟩ := GlobalTheory.T.integral_model_tangent_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hcov.1 τ A ξ β
    hβ g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ (Localization.AtPrime 𝔭.asIdeal) (algebraMap A _) yL hyL
  have hlies : LiesOn Z z := by
    intro q
    have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
    have h1 : Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) ∈ Xw := by
      have e : (yL ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          Y.j (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [← e, hyL, bot_map hinj]; exact hgen
    have h0 : ptF z (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ∈ (Z : Set (Xo.XF c)) := by
      have e : (yL ≫ r) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) =
          r (yL (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal))) := Scheme.Hom.comp_apply _ _ _
      rw [hz, e]; exact hcov.2.2.2.2.2.2.1 _ h1
    have hs : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.AtPrime 𝔭.asIdeal)) ⤳ q :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact (hs.map (ptF z).continuous).mem_closed hZc h0
  have hT : Tested z := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  have hone : evR Xo c s.sig z * evR Xo c s.inv z = 1 := by
    rw [← evR_idem hlies hT, ← s.mul_inv]
    exact (Formalism.L2.Pj.evalAt_mul _ _ _ _ _).symm
  have hU : IsUnit (evR Xo c s.sig z) := IsUnit.of_mul_eq_one _ hone
  refine ⟨hU.unit, fun k _ φ => ?_⟩
  intro alg' yy hyy y _ hy w₁' w₂' g₁ g₂ hw₁ hw₂ hg₁ hg₂
  have hyy' : yy = spMap φ ≫ yL := by
    apply (cancel_mono Y.j).1
    rw [hyy, Category.assoc, hyL, sp_sp]
  have hcomp : algebraMap c.F k = φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) := by
    have e1 : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F k) := pullback.lift_snd _ _ _
    have e2 : ptF z ≫ pullback.snd _ _ = spMap (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal)) :=
      pullback.lift_snd _ _ _
    have e3 : spMap (algebraMap c.F k) = spMap (φ.comp (algebraMap c.F (Localization.AtPrime 𝔭.asIdeal))) := by
      rw [← e1, hy, hyy', Category.assoc, Category.assoc, ← Category.assoc yL, ← hz, e2, spMap_spMap]
    have e4 := Spec.map_injective e3
    exact congrArg CommRingCat.Hom.hom e4
  let φA : Localization.AtPrime 𝔭.asIdeal →ₐ[c.F] k :=
    { φ with commutes' := fun a => (RingHom.congr_fun hcomp a).symm }
  obtain ⟨zk, hzk⟩ := GlobalTheory.FlagTan.exists_frMap φA z
  have hev : evR Xo c s.sig zk = φ (evR Xo c s.sig z) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hzk
  have hx : zk.x = y.x := by
    have e1 : y.x = ptF y ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : z.x = ptF z ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    rw [hzk.1, e1, e2, hy, hz, hyy']
    simp only [Category.assoc]
  have hv₁ : ∀ i, zk.u τ.1 i = w₁' i ≫ ν.φ := by
    intro i
    have h2 := hw₁ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₁ i) (w₁' i) (hc₁ i) h2
    rw [hzk.2.1 τ.1 i, hz₁ i, hw, Category.assoc]
  have hv₂ : ∀ i, zk.u (conjEmb τ.1) i = w₂' i ≫ ν.φ := by
    intro i
    have h2 := hw₂ i
    rw [hyy', Category.assoc, ← bcV_bcV] at h2
    have hw := GlobalTheory.T.tangent_frame_base_change Y φ yL _ _ (w₂ i) (w₂' i) (hc₂ i) h2
    rw [hzk.2.1 (conjEmb τ.1) i, hz₂ i, hw, Category.assoc]
  have key := GlobalTheory.T.flat_section_frame_invariance τ s.sig_mem zk y hx g₁ g₂ (fun i => by rw [hv₁ i]; exact hg₁ i)
    (fun i => by rw [hv₂ i]; exact hg₂ i)
  rw [hev] at key
  rw [IsUnit.unit_spec]
  exact key

end GlobalTheory.FlatModelOpen
