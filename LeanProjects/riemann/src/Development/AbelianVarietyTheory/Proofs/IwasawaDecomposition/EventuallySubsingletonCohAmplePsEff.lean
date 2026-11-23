import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersionStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := GlobalTheory.T.support_pushforward_subset_image (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
