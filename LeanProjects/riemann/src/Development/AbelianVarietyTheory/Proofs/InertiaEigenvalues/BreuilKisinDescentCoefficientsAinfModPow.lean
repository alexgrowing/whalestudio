import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CoefDescent

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_dvd_of_pow_dvd_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

variable {K : FinExt l} (bk : BK K)

theorem isUnit_evW_X : IsUnit (bk.evW X) := by
  have e : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
    simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]
  rw [e]
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 bk.flat_ne_zero

def Approx (n M : ℕ) (w : WCb l) : Prop :=
  ∃ (s : bk.S) (y : WCb l), bk.evW X ^ M * w = bk.evW s + (l : WCb l) ^ n * y

theorem Approx.mono {n M M' : ℕ} {w : WCb l} (h : Approx bk n M w) (hM : M ≤ M') : Approx bk n M' w := by
  obtain ⟨s, y, e⟩ := h
  refine ⟨X ^ (M' - M) * s, bk.evW X ^ (M' - M) * y, ?_⟩
  have : bk.evW X ^ M' = bk.evW X ^ (M' - M) * bk.evW X ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  rw [this, map_mul, map_pow]
  linear_combination bk.evW X ^ (M' - M) * e

theorem exists_approx {ι : Type} [Fintype ι] (n : ℕ) (w : ι → WCb l) (hw : ∀ i, w i ∈ bk.OE) :
    ∃ M, ∀ i, Approx bk n M (w i) := by
  classical
  choose m hm using fun i => hw i n
  refine ⟨Finset.univ.sup m, fun i => ?_⟩
  obtain ⟨s, y, e⟩ := hm i
  exact Approx.mono bk ⟨s, y, e⟩ (Finset.le_sup (Finset.mem_univ i))

theorem descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  intro l _ K bk d d' n R x a hR hx hdiv
  obtain ⟨M₁, h₁⟩ := exists_approx bk n (fun p : Fin d × Fin d' => R p.1 p.2) (fun p => hR p.1 p.2)
  obtain ⟨M₂, h₂⟩ := exists_approx bk n x hx
  obtain ⟨M, hM1, hM2⟩ : ∃ M, M₁ ≤ M ∧ M₂ ≤ M := ⟨max M₁ M₂, le_max_left _ _, le_max_right _ _⟩
  choose r yR hRe using fun i j => (h₁ (i, j)).mono bk hM1
  choose ξ z hxe using fun i => (h₂ i).mono bk hM2
  simp only at hRe
  obtain ⟨c, hc, hc1⟩ := GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin l K bk
  have hcev : ∀ s : bk.S, c (bk.ev s) = s := fun s => by
    have := hc s 1; rwa [mul_one, hc1, mul_one] at this

  have hb : ∀ i, ((l : ℕ) : Ainf l) ^ n ∣ bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j := by
    intro i
    apply pow_dvd_of_pow_dvd_inclW
    obtain ⟨q, hq⟩ := hdiv i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct] at hq
    have hs : ∑ j, bk.evW (r i j) * inclW l (a j) =
        bk.evW X ^ M * ∑ j, R i j * inclW l (a j) - (l : WCb l) ^ n * ∑ j, yR i j * inclW l (a j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(inclW l (a j))) * hRe i j
    refine ⟨bk.evW X ^ M * q - z i + ∑ j, yR i j * inclW l (a j), ?_⟩
    have e1 : inclW l (bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j) =
        bk.evW (ξ i) - ∑ j, bk.evW (r i j) * inclW l (a j) := by
      simp [BK.evW, map_sub, map_sum, map_mul]
    rw [e1, hs]
    linear_combination (-1 : WCb l) * hxe i + bk.evW X ^ M * hq
  choose b' hb' using hb
  refine ⟨fun j => c (a j), fun i => ?_⟩

  have hci : ξ i - ∑ j, r i j * c (a j) = (l : bk.S) ^ n * c (b' i) := by
    have := congrArg c (hb' i)
    rw [map_sub, map_sum, hcev] at this
    have e2 : ((l : ℕ) : Ainf l) ^ n * b' i = bk.ev ((l : bk.S) ^ n) * b' i := by
      rw [map_pow, map_natCast]
    rw [e2] at this
    simp only [hc] at this
    exact this
  have hci' := congrArg bk.evW hci
  rw [map_sub, map_sum, map_mul, map_pow, map_natCast] at hci'
  simp only [map_mul] at hci'
  have hU := (isUnit_evW_X bk).pow M
  rw [← hU.dvd_mul_left]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hs : bk.evW X ^ M * ∑ j, R i j * bk.evW (c (a j)) =
      ∑ j, bk.evW (r i j) * bk.evW (c (a j)) + (l : WCb l) ^ n * ∑ j, yR i j * bk.evW (c (a j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (bk.evW (c (a j))) * hRe i j
  refine ⟨bk.evW (c (b' i)) + z i - ∑ j, yR i j * bk.evW (c (a j)), ?_⟩
  linear_combination hxe i - hs + hci'

end GlobalTheory.CoefDescent

theorem GlobalTheory.descentCoefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i :=
  GlobalTheory.CoefDescent.descent
