import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffMemOfMemMaxPow

noncomputable section

open Filter Topology Polynomial IsLocalRing

namespace GlobalTheory.HenselSplitPS

instance isAdicComplete_maximalIdeal (D : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin D) ℂ)) (MvPowerSeries (Fin D) ℂ) := by
  have : IsPrecomplete (maximalIdeal ℂ) ℂ := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  exact { toIsHausdorff := GlobalTheory.PsCNL.haus_of_noeth _
          toIsPrecomplete := GlobalTheory.PsCNL.ps_isPrecomplete D }

theorem constantCoeff_eval (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)) (x : MvPowerSeries (Fin D) ℂ) :
    MvPowerSeries.constantCoeff (P.eval x) =
      (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).eval (MvPowerSeries.constantCoeff x) := by
  rw [eval_map, eval₂_hom]

theorem exists_lifts_of_separable : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic →
    (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable →
    ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  intro D P hP hsep
  set φ := MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ) with hφ
  set Q := P.map φ with hQ
  have hQdeg : Q.natDegree = P.natDegree := hP.natDegree_map φ
  have hcard : Q.roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hQdeg]
  let e : Fin P.natDegree ≃ Q.roots.toFinset := (Q.roots.toFinset.equivFinOfCardEq hcard).symm
  have lift : ∀ c : ℂ, c ∈ Q.roots → ∃ a : MvPowerSeries (Fin D) ℂ, P.IsRoot a ∧ φ a = c := by
    intro c hc
    have hQ0 : Q ≠ 0 := (hP.map φ).ne_zero
    have hroot : Q.eval c = 0 := (mem_roots hQ0).1 hc
    have h1 : P.eval (MvPowerSeries.C c) ∈ maximalIdeal (MvPowerSeries (Fin D) ℂ) := by
      rw [GlobalTheory.PsCNL.mem_max_iff, constantCoeff_eval, MvPowerSeries.constantCoeff_C, ← hQ, hroot]
      exact zero_mem _
    have hder : Q.derivative.eval c ≠ 0 := by
      have := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := c) (by simpa [eval₂_id] using hroot)
      simpa [eval₂_id] using this
    have h2 : IsUnit (P.derivative.eval (MvPowerSeries.C c)) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval, MvPowerSeries.constantCoeff_C,
        ← derivative_map, ← hQ]
      exact hder.isUnit
    obtain ⟨a, ha, hac⟩ := HenselianRing.is_henselian (I := maximalIdeal (MvPowerSeries (Fin D) ℂ)) P hP
      (MvPowerSeries.C c) h1 (h2.map _)
    refine ⟨a, ha, ?_⟩
    rw [GlobalTheory.PsCNL.mem_max_iff, map_sub, MvPowerSeries.constantCoeff_C, IsLocalRing.maximalIdeal_eq_bot,
      Ideal.mem_bot, sub_eq_zero] at hac
    exact hac
  choose! θ hθ using lift
  refine ⟨fun j => θ (e j), fun i j hij => ?_, fun j => (hθ _ (Multiset.mem_toFinset.1 (e j).2)).1⟩
  have hi := (hθ _ (Multiset.mem_toFinset.1 (e i).2)).2
  have hj := (hθ _ (Multiset.mem_toFinset.1 (e j).2)).2
  have : ((e i : ℂ)) = e j := by rw [← hi, ← hj]; exact congrArg φ hij
  exact e.injective (Subtype.ext this)

end GlobalTheory.HenselSplitPS

example : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) :=
  GlobalTheory.HenselSplitPS.exists_lifts_of_separable
