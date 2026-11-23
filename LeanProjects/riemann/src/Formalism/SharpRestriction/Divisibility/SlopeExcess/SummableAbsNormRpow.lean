import Mathlib
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs

noncomputable section
open NumberField IsDedekindDomain Filter Topology Asymptotics

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

section Sum
variable (K : Type) [Field K] [NumberField K]

lemma card_fib (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k).toFinset.card := by
  rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k),
    ← Nat.card_coe_set_eq]
  rfl

lemma sum_le_count (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) ≤
      (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} : ℝ) := by
  classical
  have hle := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n
  set T := hle.toFinset with hTdef
  have hT : Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} = T.card := by
    have hs : {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ n} = {I | Ideal.absNorm I ≤ n} := by
      ext I; simp
    rw [← Set.ncard_eq_toFinset_card _ hle, ← hs, ← Nat.card_coe_set_eq]
    rfl
  have hfib : ∀ k ∈ Finset.Icc 1 n,
      Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} = (T.filter (fun I => Ideal.absNorm I = k)).card := by
    intro k hk
    rw [card_fib]
    congr 1
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, hTdef]
    constructor
    · intro h; exact ⟨by rw [h]; exact (Finset.mem_Icc.1 hk).2, h⟩
    · intro h; exact h.2
  have hsum : T.card = ∑ k ∈ Finset.range (n + 1), (T.filter (fun I => Ideal.absNorm I = k)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro I hI
    simp only [hTdef, Finset.coe_range, Set.mem_Iio, Set.Finite.coe_toFinset, Set.mem_ofPred_eq] at hI ⊢
    omega
  rw [hT, hsum, Finset.sum_congr rfl (fun k hk => by rw [hfib k hk])]
  push_cast
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  · intros; positivity

lemma count_isBigO :
    (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ n} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  have h := NumberField.Ideal.tendsto_norm_le_div_atTop K
  have h1 := h.isBigO_one ℝ
  have h2 : (fun s : ℝ => (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ)) =O[atTop]
      (fun s : ℝ => s) := by
    have := h1.mul (isBigO_refl (fun s : ℝ => s) atTop)
    refine this.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      field_simp
    · filter_upwards with s; simp
  have h3 := h2.comp_tendsto tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, Real.rpow_one] using h3

lemma lseries_summable {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) (σ : ℂ) := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
  · refine (isBigO_of_le _ (fun n => ?_)).trans (count_isBigO K)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)),
      Real.norm_of_nonneg (by positivity)]
    exact sum_le_count K n
  · intro n; positivity
  · norm_num
  · simpa using hσ

theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  classical
  set c : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hc
  have hL := lseries_summable K hσ
  set a : ℕ → ℝ := fun k => ‖LSeries.term (fun n => ((c n : ℝ) : ℂ)) (σ : ℂ) k‖ with ha_def
  have ha : Summable a := hL.norm
  have ha_eq : ∀ k, k ≠ 0 → a k = c k * (k : ℝ) ^ (-σ) := by
    intro k hk
    simp only [ha_def, LSeries.term, hk, if_false]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hk)]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity)]
    simp [div_eq_mul_inv]
  refine summable_of_sum_le (fun w => by positivity) (c := ∑' k, a k) ?_
  intro u
  let N' : HeightOneSpectrum (𝓞 K) → ℕ := fun w => Ideal.absNorm w.asIdeal
  rw [← Finset.sum_fiberwise_of_maps_to (g := N') (t := u.image N')
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  calc _ ≤ ∑ k ∈ u.image N', a k := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨w0, -, rfl⟩ := Finset.mem_image.1 hk
        have hk0 : N' w0 ≠ 0 := by
          simp only [N']; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w0.ne_bot
        rw [ha_eq _ hk0]
        rw [Finset.sum_congr rfl (g := fun _ => ((N' w0 : ℕ) : ℝ) ^ (-σ))
          (fun w hw => by show ((N' w : ℕ) : ℝ) ^ (-σ) = _; rw [(Finset.mem_filter.1 hw).2])]
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [hc]
        rw [card_fib]
        exact_mod_cast Finset.card_le_card_of_injOn (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
          (fun w hw => by
            have hw' : w ∈ u.filter (fun i => N' i = N' w0) := hw
            have hmem : w.asIdeal ∈ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (N' w0)).toFinset := by
              rw [Set.Finite.mem_toFinset]; exact (Finset.mem_filter.1 hw').2
            exact hmem)
          (fun w1 _ w2 _ h => HeightOneSpectrum.ext h)
    _ ≤ ∑' k, a k := ha.sum_le_tsum _ (fun k _ => norm_nonneg _)

end Sum

end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
section Euler
variable {ι : Type} (q : ι → ℕ) (ε : ι → ℕ → ℂ) (n : ℕ)

def at' (i : ι) (j : ℕ) (s : ℂ) : ℂ := ε i j * ((q i : ℕ) : ℂ) ^ (-(2 * s + (j : ℂ)))

def ell (i : ι) (s : ℂ) : ℂ := ∑ j ∈ Finset.Icc 1 n, -Complex.log (1 - at' q ε i j s)

variable {q ε}

variable (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i : ℝ) ^ (-σ)))
include hsum

end Euler
end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
open Formalism.MainNotions.SchurIrreducible Formalism.MainNotions.PDVS MeasureTheory

section Tail
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def qS (S : Finset (Pl F)) : {w : HeightOneSpectrum (𝓞 F) // Sum.inr w ∉ S} → ℕ := fun w => qNorm w.1

variable (E) in

def εS (n M : ℕ) (S : Finset (Pl F)) : {w : HeightOneSpectrum (𝓞 F) // Sum.inr w ∉ S} → ℕ → ℂ :=
  fun w j => etaV (E := E) w.1 ^ (M + n - j)

variable (E) in

def LL (n M : ℕ) (S : Finset (Pl F)) (s : ℂ) : ℂ := ∑' w, ell (qS S) (εS E n M S) n w s

lemma εS_le (n M : ℕ) (S : Finset (Pl F)) : ∀ w j, ‖εS E n M S w j‖ ≤ 1 := by
  intro w j
  simp only [εS, norm_pow]
  unfold etaV
  split_ifs <;> simp

def eqv (S : Finset (Pl F)) (hinf : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S) :
    {w : HeightOneSpectrum (𝓞 F) // Sum.inr w ∉ S} ≃ {v : Pl F // v ∉ S} :=
  Equiv.ofBijective (fun w => ⟨Sum.inr w.1, w.2⟩)
    ⟨fun a b h => Subtype.ext (Sum.inr_injective (congrArg Subtype.val h)), fun ⟨v, hv⟩ => by
      cases v with
      | inl x => exact absurd (hinf x) hv
      | inr w => exact ⟨⟨w, hv⟩, rfl⟩⟩

end Tail

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

end Main
end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

namespace Formalism.MainNotions.DIV.Proofs
open Formalism.BasicNotions Formalism.MainNotions.PDVS Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.MainNotions.DIV.Proofs
