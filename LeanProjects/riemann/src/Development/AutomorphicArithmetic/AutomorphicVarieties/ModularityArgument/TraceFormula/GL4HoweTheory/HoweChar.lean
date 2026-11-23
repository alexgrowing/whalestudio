import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem hc_triv {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) {y : E}
    (hy : valuation E y ≤ valuation E (d : E)) : ψ y = 1 :=
  (h d).2 le_rfl y hy

private theorem hc_lc {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) :
    IsLocallyConstant (fun t : E => (ψ t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hd : valuation E (d : E) ≠ 0 := by simp
  have hm : {z : E | valuation E (z - t) < valuation E (d : E)} ∈ nhds t :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hd, fun z hz => hz⟩
  filter_upwards [hm] with z hz
  have h1 : ψ (z - t) = 1 := hc_triv h (le_of_lt hz)
  have h2 : ψ z = ψ (z - t) * ψ t := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [h2, h1, one_mul]

private theorem hc_cont {n : ℕ} : Continuous (fun x : GL (Fin n) E => GlobalTheory.Whittaker.superDiag x) := by
  unfold GlobalTheory.Whittaker.superDiag
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (Units.continuous_val).matrix_elem i j

private theorem hc_cross {n : ℕ} {ϖ : Eˣ} {a c : ℤ} {x y : GL (Fin n) E} (hx : x ∈ howeSet n ϖ a c)
    (hy : y ∈ howeSet n ϖ a c) {i j : Fin n} (hij : j.val = i.val + 1) :
    valuation E ((((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1)) i j) ≤
      valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, Matrix.sub_apply, Matrix.sub_apply]
  refine (mul_le_mul' (hx i k) (hy k j)).trans (le_of_eq ?_)
  rw [← map_mul, ← Units.val_mul, ← zpow_add]
  congr 3
  rw [hij]
  push_cast
  ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeChar :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) →
        IsLocallyConstant (fun x : GL (Fin n) E => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) ∧
        ∀ x ∈ howeSet n ϖ a c, ∀ y ∈ howeSet n ϖ a c,
          ψ (GlobalTheory.Whittaker.superDiag (x * y)) = ψ (GlobalTheory.Whittaker.superDiag x) * ψ (GlobalTheory.Whittaker.superDiag y) := by
  intro E _ _ _ _ n ϖ _ a c _ ψ hψ
  refine ⟨(UpperTheory.V.Z.Tf.L4.hc_lc hψ).comp_continuous UpperTheory.V.Z.Tf.L4.hc_cont, fun x hx y hy => ?_⟩
  set M := ((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1) with hM
  set r : E := ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, M i j with hr
  have hr1 : ψ r = 1 := by
    refine UpperTheory.V.Z.Tf.L4.hc_triv hψ ?_
    refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j hj => ?_
    exact UpperTheory.V.Z.Tf.L4.hc_cross hx hy (Finset.mem_filter.1 hj).2
  have hs : GlobalTheory.Whittaker.superDiag (x * y) =
      GlobalTheory.Whittaker.superDiag x + GlobalTheory.Whittaker.superDiag y + r := by
    simp only [GlobalTheory.Whittaker.superDiag, hr, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      have := (Finset.mem_filter.1 hj).2
      rintro rfl
      omega
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (x : Matrix (Fin n) (Fin n) E) + (y : Matrix (Fin n) (Fin n) E) + M - 1 := by
      rw [hM, Units.val_mul]
      noncomm_ring
    rw [e, Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, Matrix.add_apply, Matrix.add_apply]
  rw [hs, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hr1, mul_one]
