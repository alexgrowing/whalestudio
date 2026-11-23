import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem sum_extend_smul_starLin {M : Type} [AddCommMonoid M] [Module ℝ M] {m m' : ℕ} (s : Fin m' ↪ Fin m)
    (d : Fin m' → ℝ) (f : Fin m → M) : ∑ i, Function.extend s d 0 i • f i = ∑ j, d j • f (s j) := by
  symm
  refine Fintype.sum_of_injective s s.injective _ _ (fun i hi => ?_) fun j => by rw [s.injective.extend_apply]
  rw [Function.extend_apply' _ _ _ hi]; simp

theorem extend_nonneg_starLin {m m' : ℕ} (s : Fin m' ↪ Fin m) {d : Fin m' → ℝ} (hd : ∀ j, 0 ≤ d j) (i : Fin m) :
    0 ≤ Function.extend s d 0 i := by
  by_cases hi : ∃ j, s j = i
  · obtain ⟨j, rfl⟩ := hi; rw [s.injective.extend_apply]; exact hd j
  · rw [Function.extend_apply' _ _ _ hi]; rfl

theorem starFun_linearOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w K D hcent
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX m γ hγ hno
    have ps0 : ∀ B ∈ rcone γ, evalR (starDepth H.bar ψ w) B = 0 := fun B hB =>
      le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ B 0 hγ hB le_rfl fun v hv hp hw hin _ _ _ =>
        absurd (hno v hv hp hin) (by rw [hw]; norm_num)) (starDepth_eval_nonneg _)
    have psγ : ∀ i, (starDepth H.bar ψ w).evalZ (γ i) = 0 := fun i => by
      rw [← evalR_toReal]; exact ps0 _ (inRCone_self γ i)
    rw [linearOn_iff]
    intro c hc
    rw [starFun_evalR, (linearOn_iff ψ γ).1 hγ.linear c hc, ps0 _ ⟨c, hc, rfl⟩, add_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [starFun_evalZ, psγ i]; ring
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hh
    obtain ⟨-, hC2, hC3⟩ := hcent X hX
    have uniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
      fun v hv hp hw hin => hC3 m γ hγ v hv hp β₀ hβ₀ hp₀ hw hw₀ hin hin₀
    have hne : β₀ ≠ 0 := by
      rintro rfl
      have := hC2 0 hβ₀ hp₀ hw₀ 2 0 (by simp)
      norm_num at this
    obtain ⟨e, he, hβe⟩ := id hin₀
    have coords : ∀ (a : ℝ) (d : Fin m' → ℝ), a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) =
        ∑ i, (a * e i + Function.extend s d 0 i) • toReal (γ i) := fun a d => by
      rw [hβe, Finset.smul_sum, ← sum_extend_smul_starLin s d (fun i => toReal (γ i))]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib]
    have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hcut.2 (s j)).2 ⟨j, rfl⟩
    have psv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR (starDepth H.bar ψ w) (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a := by
      intro a d ha hd
      have hB : a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) ∈ rcone γ :=
        ⟨fun i => a * e i + Function.extend s d 0 i,
          fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i), coords a d⟩
      refine le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ _ a hγ hB ha fun v hv hp hw hin t ht hBt => ?_)
        (GlobalTheory.T.centreDepth_le_starDepth_of_cell _ H.bar ψ w X m γ _ β₀ a hγ hB hβ₀ hp₀ hw₀ hin₀ hne uniq ha ?_)
      · rw [uniq v hv hp hw hin] at hBt
        obtain ⟨g, hg, hBg⟩ := hBt
        have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) h
          (β := Sum.elim (fun j => γ (s j)) (fun o : Option (Fin m) => o.elim β₀ γ))
          (c := Sum.elim d (fun o : Option (Fin m) => o.elim (a - t) fun i => -g i)) (by
            simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
              LinearMap.id_apply, neg_smul, Finset.sum_neg_distrib]
            rw [← hBg, sub_smul]
            abel)
        simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
          hs0, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, neg_mul, Finset.sum_neg_distrib] at rel
        have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hcut.1 i)
        have hh' : (0 : ℝ) < h β₀ := by exact_mod_cast hh
        nlinarith
      · exact ⟨Function.extend s d 0, extend_nonneg_starLin s hd, by
          rw [add_sub_cancel_left, sum_extend_smul_starLin]⟩
    have psβ : (starDepth H.bar ψ w).evalZ β₀ = 1 := by
      have := psv 1 0 zero_le_one fun _ => le_rfl
      simpa using this
    have psγs : ∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0 := fun j => by
      have := psv 0 (Pi.single j 1) le_rfl fun i => by by_cases hi : i = j <;> simp [Pi.single_apply, hi]
      simpa [Pi.single_apply] using this
    have ψv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR ψ (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a * ψ.evalZ β₀ + ∑ j, d j * ψ.evalZ (γ (s j)) := by
      intro a d ha hd
      have hψβ : ψ.evalZ β₀ = ∑ i, e i * ψ.evalZ (γ i) := by
        rw [← evalR_toReal, hβe, (linearOn_iff ψ γ).1 hγ.linear e he]
      have hx := sum_extend_smul_starLin s d fun i => ψ.evalZ (γ i)
      simp only [smul_eq_mul] at hx
      rw [coords, (linearOn_iff ψ γ).1 hγ.linear _
        (fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i)), hψβ, Finset.mul_sum, ← hx]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib]
    rw [linearOn_iff]
    intro c hc
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [starFun_evalR, ψv _ _ (hc 0) (fun j => hc _), psv _ _ (hc 0) (fun j => hc _), starFun_evalZ, psβ]
    simp only [starFun_evalZ, psγs, add_zero]
    have e1 : ∑ j : Fin m', c j.succ * ((D : ℝ) * (K * ψ.evalZ (γ (s j)))) =
        D * K * ∑ j : Fin m', c j.succ * ψ.evalZ (γ (s j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; ring

end GlobalTheory.PolFan
