import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AinfK.Sep

theorem tilt_eq_zero_of_chain {l : ℕ} [hl : Fact l.Prime] (f : ℕ) (hf : 0 < f) (c : OC l) (hc : ¬ IsUnit c)
    (r : ℕ → OCb l) (hr : ∀ n, r n = r (n + 1) ^ (l ^ f)) (hd : ∀ n, c ∣ (r n).untilt) : r 0 = 0 := by
  by_contra h0
  have hne := GlobalTheory.LTTilt.untilt_ne_zero h0
  have hpos : 0 < ‖(((r 0).untilt : OC l) : ℂ_[l])‖ := norm_pos_iff.2 fun h => hne (Subtype.ext h)
  have hlt := GlobalTheory.LTTilt.norm_lt_one_of_not_isUnit c hc
  have hpow : ∀ n, r 0 = r n ^ (l ^ f) ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hr n, ← pow_mul, pow_succ']
  have hle : ∀ n, ‖(((r 0).untilt : OC l) : ℂ_[l])‖ ≤ ‖(c : ℂ_[l])‖ ^ n := fun n => by
    have h1 : c ^ ((l ^ f) ^ n) ∣ (r 0).untilt := by
      rw [hpow n, map_pow]; exact pow_dvd_pow_of_dvd (hd n) _
    have h2 := (GlobalTheory.LTTilt.mem_span_iff_norm _ _).1 (Ideal.mem_span_singleton.2 h1)
    rw [SubmonoidClass.coe_pow, norm_pow] at h2
    refine h2.trans (pow_le_pow_of_le_one (norm_nonneg _) hlt.le ?_)
    exact (Nat.lt_pow_self (Nat.one_lt_pow hf.ne' hl.out.one_lt)).le
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hlt
  exact absurd (hle n) (not_le.2 hn)

theorem chain_eq_zero {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* A) (θ : A →+* B) (p : A)
    [IsHausdorff (Ideal.span {p}) A] (hφ : φ p = p) (hp : ∀ x, x * p = 0 → x = 0)
    (hθ : ∀ y, θ p * y = 0 → y = 0)
    (hd : ∀ w : ℕ → A, (∀ n, φ (w (n + 1)) = w n) → (∀ n, θ (w n) = 0) → p ∣ w 0)
    (w : ℕ → A) (h1 : ∀ n, φ (w (n + 1)) = w n) (h2 : ∀ n, θ (w n) = 0) : w 0 = 0 := by
  have key : ∀ (k : ℕ) (w : ℕ → A), (∀ n, φ (w (n + 1)) = w n) → (∀ n, θ (w n) = 0) → p ^ k ∣ w 0 := by
    intro k
    induction k with
    | zero => intro w _ _; simp
    | succ k ih =>
      intro w h1 h2
      have hm : ∀ m, p ∣ w m := fun m => by
        simpa using hd (fun n => w (m + n)) (fun n => h1 (m + n)) (fun n => h2 (m + n))
      choose v hv using hm
      have h3 := ih v (fun n => ?_) (fun n => ?_)
      · rw [hv 0, pow_succ']
        exact mul_dvd_mul_left p h3
      · have := h1 n
        rw [hv (n + 1), hv n, map_mul, hφ] at this
        exact sub_eq_zero.1 (hp _ (by linear_combination this))
      · have := h2 n
        rw [hv n, map_mul] at this
        exact hθ _ this
  exact GlobalTheory.Per.AinfComplete.eq_zero_of_haus p _ fun n => Ideal.mem_span_singleton.2 (key n w h1 h2)

theorem red_eq_zero {l : ℕ} [Fact l.Prime] (K : FinExt l) {π : ↥(OL K)} (hπ : Irreducible π) (w : ℕ → AK K)
    (h1 : ∀ n, frobq K (w (n + 1)) = w n) (h2 : ∀ n, thetaK K (w n) = 0) : red K (w 0) = 0 :=
  tilt_eq_zero_of_chain (fK K) (NeZero.pos _) (intToOC K π) (GlobalTheory.LTTilt.not_isUnit_intToOC K hπ)
    (fun n => red K (w n))
    (fun n => (congrArg (red K) (h1 n)).symm.trans (red_frobq (w (n + 1))))
    (fun n => by
      have h := dvd_thetaK_sub hπ (w n)
      rwa [h2 n, zero_sub, dvd_neg] at h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (w : ℕ → AK K), (∀ n, frobq K (w (n + 1)) = w n) →
    (∀ n, thetaK K (w n) = 0) → w 0 = 0 := fun _ _ K w h1 h2 =>
  (exists_unif (K := K)).elim fun π hπ =>
    haveI := complete_pi hπ
    chain_eq_zero (frobq K).toRingHom (thetaK K) (inO K π) (frobq_inO K π) (eq_zero_of_mul_pi hπ)
      (fun _ h => (mul_eq_zero.1 h).resolve_left fun h0 =>
        (map_ne_zero_iff _ (intToOC_injective K)).2 hπ.ne_zero ((thetaK_inO π).symm.trans h0))
      (fun v a b => Ideal.mem_span_singleton.1 ((ker_red hπ).le (red_eq_zero K hπ v a b))) w h1 h2

end GlobalTheory.AinfK.Sep
