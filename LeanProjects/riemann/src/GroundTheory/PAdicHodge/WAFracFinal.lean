import Mathlib
import GroundTheory.PAdicHodge.WAFracLemmaO
import GroundTheory.PAdicHodge.WAFracHelp
import GroundTheory.PAdicHodge.WAFracAlg
import GroundTheory.PAdicHodge.WAKummer
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hε hζ in
theorem periodTPlus_ne_zero : periodTPlus hε ≠ 0 := fun h =>
  iotaPlus_periodTPlus_ne_zero hε hζ (by rw [h, map_zero])

include hε hζ in
theorem algebraMap_bCris_injective :
    Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) := by
  have := isDomain_bCrisPlus (p := p)
  exact IsLocalization.injective (M := Submonoid.powers (periodTPlus hε)) (BCris hε)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (periodTPlus_ne_zero hε hζ))

theorem galB_injective (σ : Gal(PadicAlgCl p/K)) : Function.Injective (galB hε σ) := by
  let := galBAction (K := K) hε
  exact MulAction.injective (α := Gal(PadicAlgCl p/K)) (β := BCris hε) σ

theorem exists_sub_eq_of_mul_eq {G R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {t : R} [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S))
    (gR : G → R →+* R) (gS : G → S →+* S) (hfg : ∀ σ x, gS σ (algebraMap R S x) = algebraMap R S (gR σ x))
    (hgS : ∀ σ, Function.Injective (gS σ)) {a b β : R} (hb : b ≠ 0) {m : ℕ} (hβ : β * b = t ^ m * a)
    (T : G → R) (hrel : ∀ σ, gR σ a * b - a * gR σ b = T σ * gR σ b * b) :
    ∃ u : S, ∀ σ, gS σ u - u = algebraMap R S (T σ) := by
  set f := algebraMap R S
  set v := IsLocalization.Away.invSelf t (S := S)
  have hvt : f t * v = 1 := IsLocalization.Away.mul_invSelf t
  refine ⟨f β * v ^ m, fun σ => ?_⟩
  have hu : f β * v ^ m * f b = f a := by
    have e : f β * v ^ m * f b = f (β * b) * v ^ m := by rw [map_mul]; ring
    rw [e, hβ, map_mul, map_pow]
    calc f t ^ m * f a * v ^ m = (f t * v) ^ m * f a := by ring
      _ = f a := by rw [hvt, one_pow, one_mul]
  have hfb : f b ≠ 0 := fun h0 => hb (hinj (by rw [h0, map_zero]))
  exact galois_sub_of_mul_eq f (gR σ) (gS σ) (hfg σ) hfb
    (fun h0 => hfb (hgS σ (by rw [h0, map_zero]))) (hrel σ) hu

set_option maxHeartbeats 1600000 in
theorem algebraMap_padic_mul_periodTPlus (q : ℚ_[p]) :
    algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * periodTPlus hε) =
      algebraMap ℚ_[p] (BCris hε) q * periodTCris hε := by
  rw [map_mul]; rfl

set_option maxHeartbeats 3200000 in
include hε hζ in

theorem exists_bCris_of_mul_eq {a b β : BCrisPlus ℂ_[p] p} (hb : b ≠ 0) {m : ℕ}
    (hβ : β * b = periodTPlus hε ^ m * a) (c : Gal(PadicAlgCl p/K) → ℚ_[p])
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (c σ) * periodTPlus hε * σ • b * b) :
    ∃ u : BCris hε, ∀ σ : Gal(PadicAlgCl p/K),
      galB hε σ u - u = algebraMap ℚ_[p] (BCris hε) (c σ) * periodTCris hε := by
  have := isDomain_bCris hε hζ
  obtain ⟨u, hu⟩ := exists_sub_eq_of_mul_eq (S := BCris hε) (t := periodTPlus hε)
    (algebraMap_bCris_injective hε hζ) (fun σ : Gal(PadicAlgCl p/K) => galPlus σ) (fun σ => galB hε σ)
    (fun σ x => galB_algebraMap hε σ x) (fun σ => galB_injective hε σ) hb hβ
    (fun σ => algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (c σ) * periodTPlus hε) hrel
  exact ⟨u, fun σ => (hu σ).trans (algebraMap_padic_mul_periodTPlus hε (c σ))⟩

variable (ρ1 : Set.Ioo (0 : ℝ) 1) (hσ : (p : ℝ)⁻¹ ≤ ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ))
  (h1 : (ρ1 : ℝ) ≤ radTwo p)

set_option maxHeartbeats 3200000 in
include hε hζ h1 in

theorem false_of_mul_eq_tTilde_pow [FiniteDimensional ℚ_[p] K] {a b : BCrisPlus ℂ_[p] p} (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b)
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε * σ • b * b)
    {m : ℕ} {Y : (𝓣).Ann ρ1 (inRad p ρ1)}
    (hY : Y * bcrisToAnn hσ b = (𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1) ^ m * bcrisToAnn hσ a) :
    False := by
  have := isDomain_bCrisPlus (p := p)

  have h3 := annNorm_frobCirc_sub_eq_zero ρ1 hσ hε hζ hb hφ hY

  obtain ⟨g, hg, hgY⟩ := exists_eigen_of_ann ρ1 (m + 1) Y h3
  have hY' : (𝔽).tildeFrob ((𝓣).ofRad ρ1 g) = (p : (𝓣).RobbaTilde) ^ (m + 1) * (𝓣).ofRad ρ1 g := by
    rw [TeichLift.TeichFrob.tildeFrob_ofRad, hg, map_mul, map_pow, map_natCast, (𝓣).ofRad_res]

  obtain ⟨-, β, -, -, hann⟩ := exists_bCrisPlus_ann m _ hY'
  have hβ : bcrisToAnn hσ β = Y := by
    rw [hann ρ1 (inRad p ρ1) hσ h1 ρ1 le_rfl g rfl, (𝓣).res_self, hgY]
  have ht := bcrisToAnn_periodTPlus hε hζ hσ h1 (le_refl (ρ1 : ℝ)) (tTildeExt p ε ρ1)
    (ofRad_tTildeExt hε hζ ρ1)
  rw [(𝓣).res_self] at ht
  have hβb : β * b = periodTPlus hε ^ m * a := by
    apply bcrisToAnn_injective hσ
    rw [map_mul, map_mul, map_pow, hβ, hY, ht]
  obtain ⟨u, hu⟩ := exists_bCris_of_mul_eq hε hζ hb hβb _ hrel
  exact not_forall_galB_sub_eq_kummerC hε hζ u hu

end WAFrac

end GroundTheory.PAdicHodge
