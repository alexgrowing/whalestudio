import Mathlib
import GroundTheory.PAdicHodge.WAFracMain
import GroundTheory.PAdicHodge.WAFracGeneric
import GroundTheory.PAdicHodge.BCrisNewton
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
  {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem injective_of_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    [IsLocalization.Away t S] (hinj : Function.Injective (algebraMap R S)) (fR : R →+* R) (fS : S →+* S)
    (hf : ∀ x, fS (algebraMap R S x) = algebraMap R S (fR x)) (hfR : Function.Injective fR) :
    Function.Injective fS := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj t x
  have h1 := congrArg fS hy
  rw [map_mul, hx, zero_mul, hf] at h1
  have hy0 : y = 0 := hfR (hinj (by rw [← h1, map_zero, map_zero]))
  rw [hy0, map_zero] at hy
  have hu : IsUnit (algebraMap R S t ^ n) := (IsLocalization.Away.algebraMap_isUnit t).pow n
  exact hu.mul_left_eq_zero.1 hy

theorem map_map_ne_zero {R E : Type*} [CommRing R] [CommRing E] (ι : R →+* E) (hι : Function.Injective ι)
    (g : R →+* R) (hg : Function.Injective g) {b : R} (hb : b ≠ 0) : ι (g b) ≠ 0 := fun h0 =>
  hb (hg (hι (by rw [h0, map_zero, map_zero])))

theorem map_zero_sub_zero_eq {S : Type*} [CommRing S] (g : S →+* S) {T : S} (hT : T = 0) :
    g 0 - 0 = T := by
  rw [hT, map_zero, sub_zero]

theorem smul_div_eq_of_cross {R E G : Type*} [CommRing R] [Field E] [Group G] [MulSemiringAction G E]
    (ι : R →+* E) (g : G → R →+* R) (hιg : ∀ σ x, ι (g σ x) = σ • ι x) {x y : R} (hy : ι y ≠ 0)
    (hgy : ∀ σ, ι (g σ y) ≠ 0) (h : ∀ σ, g σ x * y = x * g σ y) (σ : G) :
    σ • (ι x / ι y) = ι x / ι y := by
  rw [smul_div₀', ← hιg, ← hιg, div_eq_div_iff (hgy σ) hy, ← map_mul, ← map_mul, h σ]

theorem cross_of_smul_div_sub {R E G : Type*} [CommRing R] [Field E] [Group G] [MulSemiringAction G E]
    (ι : R →+* E) (hι : Function.Injective ι) (g : G → R →+* R) (hιg : ∀ σ x, ι (g σ x) = σ • ι x)
    {a b T : R} (σ : G) (hb : ι b ≠ 0) (hgb : ι (g σ b) ≠ 0) (h : σ • (ι a / ι b) - ι a / ι b = ι T) :
    g σ a * b - a * g σ b = T * g σ b * b := by
  rw [smul_div₀', ← hιg, ← hιg, div_sub_div _ _ hgb hb, div_eq_iff (mul_ne_zero hgb hb)] at h
  apply hι
  simp only [map_sub, map_mul] at h ⊢
  linear_combination h

set_option maxHeartbeats 3200000 in
include hζ in
theorem phiB_injective : Function.Injective (phiB hε) :=
  injective_of_away (periodTPlus hε) (algebraMap_bCris_injective hε hζ) (phiPlus ℂ_[p] p) (phiB hε)
    (fun x => phiB_algebraMap hε x) phiPlus_injective

set_option maxHeartbeats 4000000 in
include hζ in

theorem phiB_preperiodic_of_fixed [FiniteDimensional ℚ_[p] K] (μ : BCris hε) (hμ : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ μ = μ) :
    ∃ n d, 0 < d ∧ (phiB hε)^[n + d] μ = (phiB hε)^[n] μ := by
  obtain ⟨k, -, hk⟩ := bCris_fixed_mem_maxUnramified hε hζ μ hμ
  let ιA : BCris hε →ₐ[ℚ_[p]] 𝔹dR :=
    { toRingHom := iotaB hε hζ, commutes' := iotaB_algebraMap_padic hε hζ }
  let φA : BCris hε →ₐ[ℚ_[p]] BCris hε :=
    { toRingHom := phiB hε, commutes' := phiB_algebraMap_padic' hε }
  have halg : IsAlgebraic ℚ_[p] (ιA μ) := by
    change IsAlgebraic ℚ_[p] (iotaB hε hζ μ)
    rw [hk]
    exact (Algebra.IsAlgebraic.isAlgebraic k).algHom
      ((IsScalarTower.toAlgHom ℚ_[p] 𝔹 𝔹dR).comp (algClToBdR p))
  exact exists_iterate_eq_of_algebraic ιA (iotaB_injective hε hζ) φA halg

set_option maxHeartbeats 4000000 in
include hζ in

theorem exists_fixed_of_cross [FiniteDimensional ℚ_[p] K] (x y : BCris hε) (hy : y ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x * y = x * galB hε σ y) :
    ∃ z : BCris hε, (∀ σ : Gal(PadicAlgCl p/K), galB hε σ z = z) ∧ x = z * y := by
  have hιy : iotaB hε hζ y ≠ 0 := fun h0 => hy (iotaB_injective hε hζ (by rw [h0, map_zero]))
  have hμF : iotaB hε hζ x / iotaB hε hζ y ∈ fracBCris hε hζ :=
    div_mem (iotaB_mem_fracBCris hε hζ x) (iotaB_mem_fracBCris hε hζ y)
  have hμfix : ∀ σ : Gal(PadicAlgCl p/K), σ • (iotaB hε hζ x / iotaB hε hζ y) = iotaB hε hζ x / iotaB hε hζ y :=
    smul_div_eq_of_cross (iotaB hε hζ) (fun σ : Gal(PadicAlgCl p/K) => galB hε σ)
      (fun σ z => iotaB_galB hε hζ σ z) hιy
      (fun σ h0 => hy (galB_injective hε σ (iotaB_injective hε hζ (by rw [h0, map_zero, map_zero])))) h
  obtain ⟨k, hk, hμk⟩ := fracBCris_fixed hε hζ hμF hμfix
  obtain ⟨z, hz, hzk⟩ := exists_bCris_fixed hε hζ hk
  refine ⟨z, hz, iotaB_injective hε hζ ?_⟩
  have e1 : iotaB hε hζ z = iotaB hε hζ x / iotaB hε hζ y :=
    hzk.trans ((algClToBdRField_apply k).symm.trans hμk.symm)
  rw [map_mul, e1, div_mul_cancel₀ _ hιy]

set_option maxHeartbeats 4000000 in

theorem false_of_bCris_pair [FiniteDimensional ℚ_[p] K] {a b : BCris hε} (hb : b ≠ 0)
    (hrel : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ a * b - a * galB hε σ b =
      algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε * galB hε σ b * b) :
    False := by
  have := isDomain_bCris hε hζ
  obtain ⟨a', b', hb', hφ', hg'⟩ := exists_pair_phi (phiB hε) (phiB_injective hε hζ)
    (phiB_algebraMap_padic' hε) (fun σ : Gal(PadicAlgCl p/K) => galB hε σ) (fun σ => galB_injective hε σ)
    (fun σ q => galB_algebraMap_padic hε σ q) (fun σ x => (phiB_galB hε σ x).symm)
    (phiB_periodTCris hε) (phiB_preperiodic_of_fixed hε hζ) (exists_fixed_of_cross hε hζ)
    (fun σ => (kummerC hε hζ σ : ℚ_[p])) hb hrel
  have := isDomain_bCrisPlus (p := p)
  obtain ⟨α, β, hβ, hφ, hg⟩ := exists_pair_away (periodTPlus hε) (algebraMap_bCris_injective hε hζ)
    (phiPlus ℂ_[p] p) (phiB hε) (fun x => phiB_algebraMap hε x) (fun σ : Gal(PadicAlgCl p/K) => galPlus σ)
    (fun σ => galB hε σ) (fun σ x => galB_algebraMap hε σ x)
    (fun σ => algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε) hb' hφ'
    (fun σ => (hg' σ).trans (by rw [algebraMap_padic_mul_periodTPlus]))
  exact false_of_frac hε hζ (K := K) hg hβ hφ

set_option maxHeartbeats 4000000 in

theorem not_forall_gal_smul_sub_eq [FiniteDimensional ℚ_[p] K] {y : 𝔹dR} (hy : y ∈ fracBCris hε hζ) :
    ¬ ∀ σ : Gal(PadicAlgCl p/K), σ • y - y =
      iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε) := by
  intro h
  obtain ⟨a, b, rfl⟩ := exists_eq_div_of_mem_closure_range (iotaB hε hζ) hy
  by_cases hb : b = 0
  · refine not_forall_galB_sub_eq_kummerC hε hζ (K := K) 0 fun σ => ?_
    have h1 := h σ
    have h0 : iotaB hε hζ a / iotaB hε hζ b = 0 := by rw [hb, map_zero, div_zero]
    rw [h0, smul_zero, sub_zero] at h1
    exact map_zero_sub_zero_eq (galB hε σ) (iotaB_injective hε hζ (h1.symm.trans (map_zero _).symm))
  have hιb : iotaB hε hζ b ≠ 0 := fun h0 => hb (iotaB_injective hε hζ (by rw [h0, map_zero]))
  refine false_of_bCris_pair hε hζ (K := K) (a := a) hb fun σ => ?_
  have hιgb : iotaB hε hζ (galB hε σ b) ≠ 0 :=
    map_map_ne_zero (iotaB hε hζ) (iotaB_injective hε hζ) (galB hε σ) (galB_injective hε σ) hb
  exact cross_of_smul_div_sub (iotaB hε hζ) (iotaB_injective hε hζ)
    (fun σ : Gal(PadicAlgCl p/K) => galB hε σ) (fun σ z => iotaB_galB hε hζ σ z) σ hιb hιgb (h σ)

end WAFrac

end GroundTheory.PAdicHodge
