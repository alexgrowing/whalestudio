import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.NormConst

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  show 0 < 2 * (D.host.rdE / 2)
  unfold Formalism.BasicNotions.Host.rdE
  have h0 : (0:ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h0 (1 / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem abs_discr_F (D : D7) : |(NumberField.discr D.host.F : ℝ)| = (2 * D.host.v) ^ D.R.f := by
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  rw [h2v]
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hn := GlobalTheory.RealPlaces.finrank_E D
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  have key : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
    rw [← hn]
    unfold Formalism.BasicNotions.Host.rdE
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
    have h3 : |(NumberField.discr D.host.E : ℝ)| = (NumberField.discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
    rw [h3, sq_abs]
  have hr0 : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [mul_comm, pow_mul] at key
  exact ((pow_left_inj₀ (pow_nonneg hr0 _) (abs_nonneg _) two_ne_zero).1 key).symm

theorem card_infinitePlace_E (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem sum_range_closed (k : ℕ) : ∀ n : ℕ,
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (4 * ((i : ℝ) + 1) + 2 * k)) =
      2 * (n : ℝ) * (n + 1) * (2 * n + 1) / 3 + k * n * (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_closed k n]
    push_cast; ring

theorem sum_exponents (r k : ℕ) :
    (∑ a : Fin r, (((r - (a : ℕ)) * (4 * (r - (a : ℕ)) + 2 * k) : ℕ) : ℝ)) =
      2 * (r : ℝ) * (r + 1) * (2 * r + 1) / 3 + k * r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (((r - i) * (4 * (r - i) + 2 * k) : ℕ) : ℝ)) r,
    ← Finset.sum_range_reflect, ← sum_range_closed k r]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have e : r - (r - 1 - j) = j + 1 := by omega
  rw [e]; push_cast; ring

end GlobalTheory.CovDom.NormConst

namespace GlobalTheory.CovDom

theorem normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D
  have hv := NormConst.two_v_pos D
  refine ⟨fun a => pow_pos hv _, ?_⟩
  rw [NormConst.card_infinitePlace_E, D.what₂.card_Tau, NormConst.abs_discr_F]
  have hprod : ∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k) =
      (2 * D.host.v) ^ (∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) * (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) := by
    unfold sc
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← pow_mul]
  rw [hprod, ← pow_mul, ← Real.rpow_natCast (2 * D.host.v) D.R.f,
    ← Real.rpow_mul hv.le, ← Real.rpow_natCast (2 * D.host.v) (_ * D.R.f), ← Real.rpow_add hv]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sum, NormConst.sum_exponents]
  ring

end GlobalTheory.CovDom
