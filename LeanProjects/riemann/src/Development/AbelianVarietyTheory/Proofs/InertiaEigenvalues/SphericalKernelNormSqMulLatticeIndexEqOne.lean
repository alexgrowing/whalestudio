import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

theorem idxAt_frame : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow

theorem latIndex_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g := GlobalTheory.T.selfDualLatticeIndex_inertPlace_eq_localIndex

theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g * idxAt T w' h' g := GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod
open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.LFun.SplitTie

theorem idx_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c e → ∀ (d : Fin T.rank → ℤ) (t : GU c T.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c T.rank, ∀ k₂ ∈ KU c T.rank, latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨-, ⟨a, ha, -, hea⟩, -⟩ := he
  have hϖ : IsUnifV D.host.E w ϖ := hU.2.2.2.1
  have hK : ∀ k ∈ KU c T.rank, (k : GL (Fin T.rank) (w.adicCompletion D.host.E)) ∈ KGL w T.rank :=
    fun k hk => (Subgroup.mem_subgroupOf.1 hk).2
  rw [latIndex_inert D T v w h hw]
  refine idxAt_frame D T v w h a ha ϖ hϖ d (t : GL (Fin T.rank) (w.adicCompletion D.host.E)) ht _ (hK k₁ hk₁) _
    (hK k₂ hk₂) _ ?_
  have h1 := hea (e.symm (k₁ * t * k₂))
  rw [MulEquiv.apply_symm_apply] at h1
  rw [show ((k₁ : GL (Fin T.rank) (w.adicCompletion D.host.E)) * t * k₂) = ((k₁ * t * k₂ : GU c T.rank) : GL (Fin T.rank) (w.adicCompletion D.host.E)) by simp, h1]
  group

theorem idx_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, |d i|).toNat := by
  intro D T v w h hv e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hE := isCMExt_host D
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 T
  have hL := SelfDual.isSelfDualAt_frameLat D T v
  obtain ⟨-, w', hne, hu, -, -, -⟩ := GlobalTheory.LFun.SplitChart.split_chart_and_places hE hJ (frameLat_fg T)
    (SelfDual.isLattice_frameLat T).span_eq_top h hv hL
  have h' : w'.under (𝓞 D.host.F) = v := (hu w').2 (Or.inr rfl)
  obtain ⟨c, hc, hqc, -, he'⟩ := exists_conj_chart hE hJ hL hne h h' he
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    unfold IsUnifV at hϖ
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hO : ∀ a, c a ∈ Formalism.UG.Ov D.host.E w' ↔ a ∈ Formalism.UG.Ov D.host.E w := fun a => map_mem_Ov_iff c hc a
  have htinv : ((t⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)) : Matrix _ _ _) = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have h1 : (t : Matrix _ _ _) * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv h1]
  have hdiag : (invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [invT_val, htinv, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [map_zpow₀]
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    unfold IsUnifV at hϖ ⊢
    rw [hc, hϖ]
  have hK : ∀ k ∈ KGL w T.rank, invT c T.rank k ∈ KGL w' T.rank := fun k hk => (mem_iff_invT c hO k).1 hk
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  obtain ⟨⟨a', ha', hea'⟩, -⟩ := he'
  rw [latIndex_split D T v w w' h h' hv hne]
  have e1 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) = a * (k₁ * t * k₂) * a⁻¹ := by
    have := hea (e.symm (k₁ * t * k₂))
    rw [MulEquiv.apply_symm_apply] at this
    calc _ = a * (a⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) * a) * a⁻¹ := by group
      _ = _ := by rw [← this]
  have e2 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) =
      a' * (invT c T.rank k₁ * invT c T.rank t * invT c T.rank k₂) * a'⁻¹ := by
    have := hea' (e.symm (k₁ * t * k₂))
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul, map_mul] at this
    calc _ = a' * (a'⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) * a') * a'⁻¹ := by group
      _ = _ := by rw [← this]
  have hs : ∑ i, |d i| = (∑ i, max (d i) 0) + ∑ i, max (-d i) 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (d i) with hd | hd
    · rw [abs_of_nonneg hd, max_eq_left hd, max_eq_right (by omega), add_zero]
    · rw [abs_of_nonpos hd, max_eq_right hd, max_eq_left (by omega), zero_add]
  rw [idxAt_frame D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ _ e1,
    idxAt_frame D T v w' h' a' ha' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hK k₁ hk₁) _ (hK k₂ hk₂) _ e2, hqc,
    ← pow_add, hs, Int.toNat_add (Finset.sum_nonneg fun i _ => le_max_right _ _) (Finset.sum_nonneg fun i _ => le_max_right _ _)]
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod

theorem exists_over {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
      (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  exact ⟨⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [← e, h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)])⟩,
    HeightOneSpectrum.ext e⟩

theorem norm_split (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m s : ℤ) (hs : 0 ≤ s) :
    ‖z ^ m * (q : ℂ) ^ (-((N : ℂ) / 2) * (s : ℂ))‖ ^ 2 * ((q ^ s.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, show (q : ℂ) = ((q : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq']
  have hre : (-((N : ℂ) / 2) * (s : ℂ)).re = -((N : ℝ) / 2) * s := by
    simp [Complex.mul_re]
  rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) s.toNat,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_add hq']
  have : (s.toNat : ℝ) = s := by exact_mod_cast Int.toNat_of_nonneg hs
  rw [this]
  have : -((N : ℝ) / 2) * s * ((2 : ℕ) : ℝ) + s * N = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem norm_inert (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m : ℤ) (hm : 0 ≤ m) :
    ‖(z * ((q : ℂ) ^ N)⁻¹) ^ m‖ ^ 2 * (((q ^ 2) ^ m.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp only [Int.toNat_natCast, zpow_natCast, norm_pow, norm_mul, norm_inv, hz, one_mul, Complex.norm_natCast]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
  rw [show N * (k * 2) = 2 * (k * N) by ring]
  exact inv_mul_cancel₀ (pow_ne_zero _ hq'.ne')

theorem sq_norm_mul_latIndex : ∀ (D : D7) (T : HSp D) (N : ℕ) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.FinZeta.Gv T v → ℂ), GlobalTheory.FinZeta.IsLocKer T N (GlobalTheory.LFun.val χ) v φ → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → ∀ a : GlobalTheory.FinZeta.Gv T v, ‖φ a‖ ^ 2 * (latIndex T (GlobalTheory.FinZeta.embV T v a) : ℝ) ^ N = 1 := by
  intro D T N χ v φ hφ _ a
  obtain ⟨w, h⟩ := exists_over (D := D) v
  by_cases hs : IsSplit (E := D.host.E) v
  · obtain ⟨e, he⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).1 hs
    have hk := (hφ w h).1 hs e he
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := D.host.E) w
    obtain ⟨d, -, k₁, hk₁, k₂, hk₂, ec⟩ :=
      Formalism.UG.Final.CartanDecomp D.host.E w T.rank ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ (e a)
    have htd : (k₁⁻¹ * e a * k₂⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 =
        Matrix.diagonal (fun i => ϖ ^ d i) := by
      rw [Units.val_mul, Units.val_mul, ec]
      simp [Matrix.mul_assoc]
      rfl
    have ha : a = e.symm (k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂) := by
      rw [show k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂ = e a by group, MulEquiv.symm_apply_apply]
    have hv := hk ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_split D T v w h hs e he ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    exact norm_split _ (Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ _ (Finset.sum_nonneg fun i _ => abs_nonneg (d i))
  · have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
    obtain ⟨hw, -, hch⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).2 hs
    obtain ⟨-, ⟨c, hc, -⟩, -, hN, H⟩ := hI.2 w h hw
    obtain ⟨ϖ, hU⟩ := (H c hc).1
    obtain ⟨e, he⟩ := hch c hc
    have hk := (hφ w h).2 hw c ϖ e hU he
    obtain ⟨d, t, -, ht, k₁, hk₁, k₂, hk₂, ea⟩ := GlobalTheory.LFun.cartanU hU (e a)
    have ha : a = e.symm (k₁ * t * k₂) := by rw [← ea, MulEquiv.symm_apply_apply]
    have hv := hk d t ht k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_inert D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂]
    have hq : qV D.host.E w = qV D.host.F v ^ 2 := hN
    rw [hq]
    exact norm_inert _ (Nat.pos_of_ne_zero fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ (Finset.sum_nonneg fun i _ => le_max_right _ _)

end GlobalTheory.LocKerMod
