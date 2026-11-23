import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.WeilfunCore

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor PositivityTheory.HtPt.Weilfun

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

private theorem cubN_succ_chow_mahler_families (k : ℕ) (a m x : A) :
    cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x := by
  simp only [cubN, Finset.prod_range_succ]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (y x : A) :
    cubN θ (a + b) 1 y x = cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) := by
  induction b with
  | zero =>
    have e : θ (y ^ a) 1 x = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ b ih =>
    rw [← Nat.add_assoc, cubN_succ_chow_mahler_families (a + b), cubN_succ_chow_mahler_families b, ih, _root_.one_mul, _root_.one_mul]
    have c := h.coc (y ^ a) (y ^ b) y x
    rw [← pow_add, ← pow_succ] at c
    calc cubN θ a 1 y x * (θ (y ^ a) (y ^ b) x * cubN θ b 1 y x) * θ (y ^ (a + b)) y x
        = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ (a + b)) y x * θ (y ^ a) (y ^ b) x) := by ac_rfl
      _ = cubN θ a 1 y x * cubN θ b 1 y x * (θ (y ^ a) (y ^ (b + 1)) x * θ (y ^ b) y x) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_mul (h : IsCub θ) (N M : ℕ) (y x : A) :
    cubN θ (N * M) 1 y x = cubN θ N 1 (y ^ M) x * cubN θ M 1 y x ^ N := by
  induction N with
  | zero => simp [cubN]
  | succ N ih =>
    rw [Nat.succ_mul, cubN_add h (N * M) M y x, ih, cubN_succ_chow_mahler_families N, pow_succ (cubN θ M 1 y x) N,
      _root_.one_mul, show (y ^ M) ^ N = y ^ (N * M) by rw [← pow_mul, mul_comm]]
    ac_rfl

theorem cubN_mul_of_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ (N * M) 1 x y = cubN θ N 1 x y ^ M := by
  rw [show N * M = M * N from Nat.mul_comm N M, cubN_mul h M N x y, hx]
  have e : cubN θ M 1 1 y = 1 := by
    unfold cubN
    exact Finset.prod_eq_one fun i _ => by rw [one_pow, _root_.one_mul, h.face]
  rw [e, _root_.one_mul]

private theorem cubN_eq_theta_pow_mul_cubN_one (h : IsCub θ) (k : ℕ) (a x z : A) :
    cubN θ k a x z = θ a (x ^ k) z * cubN θ k 1 x z := by
  induction k with
  | zero =>
    have e : θ a 1 z = 1 := by rw [h.s01, h.face]
    simp [cubN, e]
  | succ k ih =>
    rw [cubN_succ_chow_mahler_families k a, cubN_succ_chow_mahler_families k 1, ih, _root_.one_mul]
    have c := h.coc a (x ^ k) x z
    rw [← pow_succ] at c
    calc θ a (x ^ k) z * cubN θ k 1 x z * θ (a * x ^ k) x z
        = cubN θ k 1 x z * (θ (a * x ^ k) x z * θ a (x ^ k) z) := by ac_rfl
      _ = cubN θ k 1 x z * (θ a (x ^ (k + 1)) z * θ (x ^ k) x z) := by rw [c]
      _ = _ := by ac_rfl

private theorem theta_pow_mul_prod_range_eq_prod (h : IsCub θ) (a x y : A) (M : ℕ) :
    θ a x (y ^ M) * ∏ j ∈ Finset.range M, θ (y ^ j) x y = ∏ j ∈ Finset.range M, θ (a * y ^ j) x y := by
  induction M with
  | zero =>
    rw [pow_zero, Finset.prod_range_zero, Finset.prod_range_zero, _root_.mul_one, h.s12, h.s01, h.face]
  | succ M ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih]
    have c := h.coc a (y ^ M) y x
    rw [← pow_succ, h.s12 (a * y ^ M) y x, h.s12 a (y ^ M) x, h.s12 a (y ^ (M + 1)) x,
      h.s12 (y ^ M) y x] at c
    calc θ a x (y ^ (M + 1)) * ((∏ j ∈ Finset.range M, θ (y ^ j) x y) * θ (y ^ M) x y)
        = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ a x (y ^ (M + 1)) * θ (y ^ M) x y) := by ac_rfl
      _ = (∏ j ∈ Finset.range M, θ (y ^ j) x y) * (θ (a * y ^ M) x y * θ a x (y ^ M)) := by rw [c]
      _ = _ := by ac_rfl

theorem cubN_pow (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N = cubN θ N 1 x y ^ M := by
  have hD : cubN θ M 1 y x = ∏ j ∈ Finset.range M, θ (y ^ j) x y := by
    unfold cubN
    exact Finset.prod_congr rfl fun j _ => by rw [_root_.one_mul, h.s12]
  have hC : cubN θ N 1 x (y ^ M) * cubN θ M 1 y x ^ N =
      ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (x ^ i * y ^ j) x y := by
    rw [hD, show (∏ j ∈ Finset.range M, θ (y ^ j) x y) ^ N =
        ∏ _i ∈ Finset.range N, ∏ j ∈ Finset.range M, θ (y ^ j) x y by
      rw [Finset.prod_const, Finset.card_range]]
    unfold cubN
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [_root_.one_mul, theta_pow_mul_prod_range_eq_prod h]
  rw [hC, Finset.prod_comm,
    show cubN θ N 1 x y ^ M = ∏ _j ∈ Finset.range M, cubN θ N 1 x y by
      rw [Finset.prod_const, Finset.card_range]]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e := cubN_eq_theta_pow_mul_cubN_one h N (y ^ j) x y
  rw [hx, h.s01 (y ^ j) 1 y, h.face, _root_.one_mul] at e
  rw [← e]
  unfold cubN
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem wq_level (h : IsCub θ) (N M : ℕ) {x : A} (hx : x ^ N = 1) (y : A) :
    wq θ (N * M) x y = wq θ N x (y ^ M) := by
  unfold wq
  rw [cubN_mul h N M y x, cubN_mul_of_pow h N M hx y, ← cubN_pow h N M hx y,
    mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

end Alg

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

theorem weilUnit_level (c : CubicalStr G L) (N M n : ℕ) (hn : n = N * M) {T : Over S} {x y x' y' : T ⟶ G}
    (hx : x ^ N = 1) (hy : y ^ N = 1) (hx' : x' ^ n = 1) (hy' : y' ^ n = 1) (e₁ : x = x') (e₂ : y = y' ^ M) :
    weilUnit c N T x y hx hy = weilUnit c n T x' y' hx' hy' := by
  subst hn e₁ e₂
  apply Units.ext
  apply fn_ext
  intro z _
  obtain ⟨J, hJ⟩ := exists_good_at L z
  have h1 := gm_id_weilUnit c N hx hy z hJ
  have h2 := gm_id_weilUnit c (N * M) hx' hy' z hJ
  rw [wq_level (isCub_cubV c hJ) N M hx] at h2
  have h3 := congrArg Units.val (h1.trans h2.symm)
  simp only [gm_val (𝟙 T.left) z ⊤ trivial] at h3
  simp only [gs, dif_pos (show (𝟙 T.left : T.left ⟶ T.left) z ∈ (⊤ : T.left.Opens) from trivial)]
  exact h3

end PositivityTheory.Xgn.TestGroupPoint
