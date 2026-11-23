import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDiscStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_map_eq (l : ℕ) [Fact l.Prime] {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (u : A) (u' : A') (ρ ρ' : ℝ≥0) (h0 : 0 < ρ') (hu : f u = u') (h : ρ' ≤ ρ) :
    ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap f F := by
  have h1 : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    have := norm_toDisc_pow_le (l := l) (u := u') 1 h0
    rw [pow_one, pow_one] at this
    rw [hu]
    exact this.trans (by exact_mod_cast h)
  exact ⟨_, isDiscMap_map f h1⟩

theorem BK.rho_zero_pos {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

theorem norm_E_mul_of_topBasis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (y : Disc l (s X) ρ) :
    ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  have hρ : 0 < ρ := bk.rho_zero_pos.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨cD, -, hmul, hle, -, -, hsup, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  have key : ∀ i, ‖cD i (toDisc l (s X) ρ (s bk.E) * y)‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖cD i y‖ := fun i => by
    rw [← hj.ext, hmul, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1]
  refine le_antisymm (hsup _ _ (by positivity) fun i => ?_) ?_
  · rw [key]
    exact mul_le_mul_of_nonneg_left (hle i y) hρ'.le
  · rw [← le_div_iff₀' hρ']
    refine hsup _ _ (by positivity) fun i => ?_
    rw [le_div_iff₀' hρ', ← key]
    exact hle _ _

theorem E_dvd_of_topBasis (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (hR : IsDiscMap (RingHom.id A) R) (y : Disc l (s X) ρ)
    (hy : toDisc l (s X) bk.ρ₀ (s bk.E) ∣ R y) : toDisc l (s X) ρ (s bk.E) ∣ y := by
  have hρ₀ := bk.rho_zero_pos
  have hρ : 0 < ρ := hρ₀.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨j₀, hj₀⟩ := exists_discMap_of_map_eq l s X (s X) bk.ρ₀ bk.ρ₀ hρ₀ rfl le_rfl
  obtain ⟨RS, hRS⟩ := exists_discMap_of_map_eq l (RingHom.id bk.S) X X ρ bk.ρ₀ hρ₀ rfl h0
  obtain ⟨cD, hc, hmul, hle, hnull, -, hsup, hex, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  obtain ⟨cD₀, hc₀, hmul₀, hle₀, -, -, -, -, -⟩ :=
    GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ hρ₀ (h0.trans_lt h1) j₀ hj₀
  have comm : ∀ i x, cD₀ i (R x) = RS (cD i x) := fun i => by
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.1 (bk.DS bk.ρ₀) (fun z hz => by
        rw [nsmul_eq_mul] at hz
        exact (isUnit_l_disc l (X : bk.S) bk.ρ₀).mul_right_eq_zero.1 hz)
      ((cD₀ i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i))
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hle₀ i (R x)).trans (hR.norm_le x)).trans (one_mul _).ge)
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hRS.norm_le (cD i x)).trans (hle i x)).trans (one_mul _).ge)
      (fun a => by
        change cD₀ i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
        rw [hR.ext, hc, hRS.ext, RingHom.id_apply, RingHom.id_apply, hc₀])
    exact fun x => DFunLike.congr_fun h x
  obtain ⟨w, hw⟩ := hy
  have hd : ∀ i, ∃ z, cD i y = toDisc l (X : bk.S) ρ bk.E * z := fun i =>
    GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc l K bk ρ h0 h1 RS hRS _ ⟨cD₀ i w, by rw [← comm, hw, ← hj₀.ext, hmul₀]⟩
  choose z hz using hd
  have hzn : Filter.Tendsto z Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_zero_iff_norm_tendsto_zero.1 (hnull y)).div_const ((ρ : ℝ) ^ bk.Ep.natDegree)
    rw [zero_div] at h
    refine h.congr fun i => ?_
    rw [hz, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1, mul_div_cancel_left₀ _ hρ'.ne']
  obtain ⟨y', hy'⟩ := hex z hzn
  refine ⟨y', ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine hsup _ 0 le_rfl fun i => ?_
  rw [map_sub, ← hj.ext, hmul, hy', hz, sub_self, norm_zero]

theorem div_E_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 →
    (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧
    ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ),
      toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  intro l _ K bk A _ s ι TB ρ h0 h1
  refine ⟨norm_E_mul_of_topBasis l K bk A s ι TB ρ h0 h1, fun R hR h => ?_⟩
  have hρ' : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast bk.rho_zero_pos) _
  induction h with
  | zero => intro y _; rw [pow_zero]; exact one_dvd _
  | succ h ih =>
    intro y hy
    obtain ⟨y', rfl⟩ := E_dvd_of_topBasis l K bk A s ι TB ρ h0 h1 R hR y
      ((dvd_pow_self _ (Nat.succ_ne_zero h)).trans hy)
    obtain ⟨w, hw⟩ := hy
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih y' ⟨w, ?_⟩)
    rw [map_mul, hR.ext, RingHom.id_apply, pow_succ', mul_assoc, ← sub_eq_zero, ← mul_sub] at hw
    have h2 := norm_E_mul_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl (h0.trans_lt h1)
      (R y' - toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * w)
    rw [hw, norm_zero] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hρ'.ne'))

end GlobalTheory.BSP
