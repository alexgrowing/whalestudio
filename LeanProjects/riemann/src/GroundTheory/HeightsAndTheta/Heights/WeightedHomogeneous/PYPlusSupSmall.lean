import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace YPlusSupSmall

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem eval_map_int {σ R : Type*} [CommRing R] (w : σ → R) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom R) p) = aeval w p := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem evalCone_unflatCone {κ : Type} {m : κ → ℕ} {R : Type*} [CommRing R] (w : Coord m → R)
    (p : MvPolynomial (Coord m) ℤ) : evalCone (unflatCone w) p = aeval w p := by
  rw [← eval_map_flatCone, flatCone_unflatCone, eval_map_int]

theorem exps {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) {m : Coord D.extSizes →₀ ℕ}
    (hm : m ∈ f.support) : (∀ k i, m ⟨some k, i⟩ = 0) ∧ ∑ j, m ⟨none, j⟩ = τ := by
  refine ⟨fun k i ↦ ?_, ?_⟩
  · have h := hf m hm (some k)
    rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
    exact h i (Finset.mem_univ _)
  · have h := hf m hm none
    rwa [Pi.single_eq_same] at h

theorem scale {R : Type*} [CommRing R] {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ)) (u w : Coord D.extSizes → R)
    (α β : R) (huw : ∀ j : Fin (D.size + 1), α * u ⟨none, j⟩ = β * w ⟨none, j⟩) :
    α ^ τ * aeval u f = β ^ τ * aeval w f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨h0, hτ⟩ := exps D hf hm
  have key : ∀ (v : Coord D.extSizes → R) (γ : R),
      γ ^ τ * ∏ p, v p ^ m p = ∏ j, (γ * v ⟨none, j⟩) ^ m ⟨none, j⟩ := by
    intro v γ
    rw [Fintype.prod_sigma, Fintype.prod_option]
    simp only [h0, pow_zero, Finset.prod_const_one, mul_one]
    rw [← hτ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  rw [mul_left_comm (α ^ τ), mul_left_comm (β ^ τ), key u α, key w β]
  exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ congrArg (· ^ m ⟨none, j⟩) (huw j))

theorem subst_homog {τ : ℕ} {f : MvPolynomial (Coord D.extSizes) ℤ}
    (hf : Geo.IsMultiHomog (ι := blockIdx D.extSizes) f (Pi.single none τ))
    (G : Coord D.extSizes → MvPolynomial (Coord n) ℤ) (e : ι → ℕ)
    (hG : ∀ v, IsWeightedHomogeneous (coordDeg n) (G v) e) :
    IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) := by
  rw [aeval_def, eval₂_eq']
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun v ↦ G v ^ m v) (fun v ↦ m v • e)
    fun v _ ↦ (hG v).pow (m v)
  have hs : ∑ v, m v • e = τ • e := by
    obtain ⟨h0, hτ⟩ := exps D hf hm
    rw [← Finset.sum_smul, Fintype.sum_sigma, Fintype.sum_option]
    simp [h0, hτ]
  rw [hs] at hp
  have hC : IsWeightedHomogeneous (coordDeg n) (algebraMap ℤ (MvPolynomial (Coord n) ℤ) (coeff m f)) 0 := by
    rw [algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  simpa using hC.mul hp

def newSubst (g : Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) :
    Coord D.extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => g j
  | ⟨some _, _⟩ => 0

end YPlusSupSmall

open YPlusSupSmall in

theorem YPlusSupSmall.proof (hForms : ChartFormsAlt.Statement) (hPts : ConePoints.Statement) :
    YPlusSupSmall.Statement := by
  intro ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hInd _ hsmall f hf hfs z hz
  classical
  obtain ⟨d, hd⟩ := hForms ι n P D
  obtain ⟨g, hg⟩ := hd d le_rfl
  have hζ : D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) :=
    D.oldFlat_mem_mcPts y x' z hz

  have hw : unflatCone z ∈ D.extPoints := by
    refine ⟨(blockNonzero_unflatCone_iff z).mpr hz.1, fun p hp ↦ ?_⟩
    rw [evalCone_unflatCone, ← eval_map_int]
    exact hz.2 p (hR.ext_eq ▸ hp)
  obtain ⟨-, la, hla, hrel⟩ := (hPts ι n P D d g hg).2 _ hw

  obtain ⟨c, hc⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z ⟨some k, c k⟩ ≠ 0 :=
    ⟨fun k ↦ (hz.1 (some k)).choose, fun k ↦ (hz.1 (some k)).choose_spec⟩
  have hmz : aeval (D.oldFlat z) (chartMonomial (n := n) c d) ≠ 0 := by
    simp only [chartMonomial, map_prod, map_pow, aeval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hlive : P.IsLive c := by
    intro k hk
    have h := hζ.2 _ (by rw [← hR.ideal_eq]; exact hk)
    rw [eval_map_int, aeval_X] at h
    exact hc k h

  obtain ⟨e, he⟩ : ∃ e : ι → ℕ, ∀ k, (e k : ℤ) = d k + D.deg k :=
    ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)⟩
  have hgh : ∀ j, IsWeightedHomogeneous (coordDeg n) (g c j) e := by
    intro j
    obtain ⟨δ, hδ, hδe⟩ := hg.homog c j
    have : δ = e := funext fun k ↦ by have h1 := hδe k; have h2 := he k; omega
    rwa [← this]
  have hmh : IsWeightedHomogeneous (coordDeg n) (chartMonomial (n := n) c d) d :=
    isWeightedHomogeneous_chartMonomial c d

  have hval : ∀ j, aeval y (g c j) = x' j * aeval y (chartMonomial c d) := fun j ↦
    (hR.reads j (g c j) (chartMonomial c d) e d (hgh j) hmh fun k ↦ he k).mpr
      (by rw [hg.value c hlive j, mul_comm])

  have hrelj : ∀ j : Fin (D.size + 1), aeval (D.oldFlat z) (chartMonomial c d) * z ⟨none, j⟩ =
      la * aeval (D.oldFlat z) (g c j) := by
    intro j
    have hold : D.basePart₂ (unflatCone z) = unflatCone (D.oldFlat z) := rfl
    have h := hrel c (by rw [hold, evalCone_unflatCone]; exact hmz) j
    rw [hold, evalCone_unflatCone, evalCone_unflatCone] at h
    change z ⟨none, j⟩ = _ at h
    rw [h]
    field_simp

  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (D.size + 1), z ⟨none, j⟩ ≠ 0 := hz.1 none
  have hAp : Ap.h z = ‖la‖ * N.h (D.oldFlat z) := by
    have h := hInd j₀ (g c j₀) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mpr (hgh j₀))
      ((geoMultiHomog_iff _ _).mpr hmh) (fun k ↦ by rw [hNa]; exact he k)
      (by rw [hval, mul_comm]) z hz
    rw [eval_map_int, eval_map_int] at h
    have hgz : aeval (D.oldFlat z) (g c j₀) ≠ 0 := by
      intro h0
      have h1 := hrelj j₀
      rw [h0, mul_zero] at h1
      exact mul_ne_zero hmz hj₀ h1
    have h2 := congrArg norm (hrelj j₀)
    rw [norm_mul, norm_mul] at h2
    apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hgz)
    linear_combination -h + N.h (D.oldFlat z) * h2

  set G := newSubst D (g c) with hG
  have hcomp : ∀ {R : Type} [CommRing R] (w : Coord n → R) (p : MvPolynomial (Coord D.extSizes) ℤ),
      aeval w (aeval G p) = aeval (fun v ↦ aeval w (G v)) p := fun w p ↦ by
    rw [← AlgHom.comp_apply, comp_aeval]
  have hFh : IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) :=
    subst_homog D hf G e (by rintro ⟨_ | k, i⟩; exacts [hgh i, isWeightedHomogeneous_zero _ _ _])
  have hFy : aeval y (aeval G f) = s * aeval y (chartMonomial c d ^ τ) := by
    have h := scale D hf (fun v ↦ aeval y (G v)) (D.plusCoord y x') 1 (aeval y (chartMonomial c d))
      (fun j ↦ by
        change 1 * aeval y (g c j) = aeval y (chartMonomial c d) * x' j
        rw [one_mul, hval, mul_comm])
    rw [one_pow, one_mul, hfs] at h
    rw [hcomp, h, map_pow, mul_comm]
  have hb := hsmall (τ • e) (τ • d) (aeval G f) (chartMonomial c d ^ τ) (D.oldFlat z)
    ((geoMultiHomog_iff _ _).mpr hFh) ((geoMultiHomog_iff _ _).mpr (hmh.pow τ))
    (fun k ↦ by simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k, hNa]; ring) hFy hζ
  rw [eval_map_int, eval_map_int, map_pow, norm_pow] at hb

  have hsc := scale D hf z (fun v ↦ aeval (D.oldFlat z) (G v)) (aeval (D.oldFlat z) (chartMonomial c d)) la
    (fun j ↦ hrelj j)
  rw [← hcomp] at hsc
  suffices hfin : ‖aeval z f‖ ≤ Ap.h z ^ τ from (congrArg norm (eval_map_int z f)).trans_le hfin
  have hpos : 0 < ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ := pow_pos (norm_pos_iff.mpr hmz) τ
  refine le_of_mul_le_mul_left ?_ hpos
  calc ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * ‖aeval z f‖
      = ‖la‖ ^ τ * ‖aeval (D.oldFlat z) (aeval G f)‖ := by
        rw [← norm_pow, ← norm_pow, ← norm_mul, ← norm_mul, hsc]
    _ ≤ ‖la‖ ^ τ * (‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * N.h (D.oldFlat z) ^ τ) := by
        gcongr
    _ = ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * Ap.h z ^ τ := by
        rw [hAp, mul_pow]; ring

end

end GroundTheory.Heights₂.Heights
