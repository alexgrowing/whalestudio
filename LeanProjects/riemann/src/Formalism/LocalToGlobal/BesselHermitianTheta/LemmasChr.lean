import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem norm_idF (a : (AF D.host.F)ˣ) :
    Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
  apply Units.ext
  have b : Module.Basis (Fin 2) D.host.F D.host.E := Module.finBasisOfFinrankEq _ _ D.sp.cm.deg2
  have := Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF D.host.F) b) (a : AF D.host.F)
  simpa [idF] using this

theorem eta_sq {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h1 := h.2.2.1 (idF D a)
  rw [norm_idF, map_pow] at h1
  exact h1

theorem eta_pow_parity {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) {n m : ℕ}
    (e : n % 2 = m % 2) : η a ^ n = η a ^ m := by
  have h2 := eta_sq h a
  rw [← Nat.mod_add_div n 2, ← Nat.mod_add_div m 2, pow_add, pow_add, pow_mul, pow_mul, h2, one_pow, one_pow, e]

variable {χ χ' : (AE D)ˣ →* Circle} {n m : ℕ}

theorem resEta_parity (h : ResEta D χ n) (e : n % 2 = m % 2) : ResEta D χ m := by
  refine ⟨h.1, fun η hη b => ?_⟩
  rw [h.2 η hη b]
  exact eta_pow_parity hη b e

theorem resEta_mul (h : ResEta D χ n) (h' : ResEta D χ' m) : ResEta D (χ * χ') (n + m) := by
  refine ⟨h.1, fun η hη b => ?_⟩
  rw [MonoidHom.mul_apply, h.2 η hη b, h'.2 η hη b, pow_add]

theorem resEta_inv (h : ResEta D χ n) : ResEta D χ⁻¹ n := by
  refine ⟨h.1, fun η hη b => ?_⟩
  rw [MonoidHom.inv_apply, h.2 η hη b, ← inv_pow]
  congr 1
  have h2 := eta_sq hη b
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h2)

theorem resEta_not_both (h0 : ResEta D χ 0) (h1 : ResEta D χ 1) : False := by
  obtain ⟨η, hη⟩ := h0.1
  apply hη.2.2.2
  refine MonoidHom.ext fun a => ?_
  have e0 := h0.2 η hη a
  have e1 := h1.2 η hη a
  rw [pow_zero] at e0
  rw [pow_one] at e1
  rw [MonoidHom.one_apply, ← e1, e0]

variable {X : ThetaX D}

theorem col_ok (T : ThetaTied D X) (μ : D.what₂.Tup) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ D.R.m) (n : ℕ) (hn : Even n) :
    ResEta D (T.eChr (X.chrOf μ s)) n :=
  resEta_parity (T.chrOf_res μ s h1 h2) (by rw [Nat.even_iff.1 hn])

theorem carY_ok (T : ThetaTied D X) (μ : D.what₂.Tup) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ D.R.m) (i n : ℕ)
    (hn : Even n ↔ Odd i) : ResEta D (T.eChr (X.carY μ s i)) n := by
  unfold ThetaX.carY
  split_ifs with hi
  · have hn' : n % 2 = 1 := by
      rcases Nat.even_or_odd n with h | h
      · exact absurd hi (Nat.not_even_iff_odd.2 (hn.1 h))
      · exact Nat.odd_iff.1 h
    rw [map_mul, map_inv]
    exact resEta_parity (resEta_mul (T.chrOf_res μ s h1 h2) (resEta_inv T.etaT_res)) (by rw [hn'])
  · exact col_ok T μ s h1 h2 n (hn.2 (Nat.not_even_iff_odd.1 hi))

theorem rank_X (X : ThetaX D) (j : ℕ) (hj : j ≤ D.R.m) : (D.sp.X j).rank = D.R.k + j * (D.R.t + 1) := D.sp.X_rank j hj

theorem rank_Y (X : ThetaX D) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.Y i).rank = D.R.r + i * D.R.t := D.sp.Y_rank i hi

theorem r_odd (D : D7) : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  show D.R.k + D.R.m - 1 = 2 * (a + b - 1) + 1
  omega

theorem col_lift_ok (T : ThetaTied D X) (μ : D.what₂.Tup) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ D.R.m) (j : ℕ) (hj : j ≤ D.R.m) :
    ResEta D (T.eChr (X.chrOf μ s)) (D.sp.X j).rank := by
  apply col_ok T μ s h1 h2
  rw [rank_X X j hj]
  exact D.R.k_even.add (D.R.t_odd.add_one.mul_left j)

theorem row_lift_ok (T : ThetaTied D X) (μ : D.what₂.Tup) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ D.R.m) (i : ℕ) (hi : i ≤ D.R.m) :
    ResEta D (T.eChr (X.carY μ s i)) (D.sp.Y i).rank := by
  apply carY_ok T μ s h1 h2
  rw [rank_Y X i hi]
  have hr := r_odd D
  have ht := D.R.t_odd
  constructor
  · intro he
    by_contra hi'
    rw [Nat.not_odd_iff_even] at hi'
    exact (Nat.not_even_iff_odd.2 (hr.add_even (hi'.mul_right _))) he
  · intro ho
    exact hr.add_odd (ho.mul ht)

theorem rank_X_ne (X : ThetaX D) (j : ℕ) (hj : j < D.R.m) : (D.sp.X j).rank ≠ (D.sp.X (j + 1)).rank := by
  rw [rank_X X j hj.le, rank_X X (j + 1) hj, Nat.succ_mul]
  generalize j * (D.R.t + 1) = q
  omega

theorem rank_Y_ne (X : ThetaX D) (j : ℕ) (hj : j < D.R.m) : (D.sp.Y (j + 1)).rank ≠ (D.sp.Y j).rank := by
  rw [rank_Y X (j + 1) hj, rank_Y X j hj.le, Nat.succ_mul]
  have ht := D.R.t_odd.pos
  generalize j * D.R.t = q
  omega

end Formalism.L2.Theta

end
