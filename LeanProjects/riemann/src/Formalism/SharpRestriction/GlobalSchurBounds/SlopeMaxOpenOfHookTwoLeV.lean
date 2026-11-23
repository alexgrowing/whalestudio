import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
import Formalism.GradedWeylDivisibility.StatementB

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions NumberField

section B23b

def stdGram {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    Formalism.GradedWeylDivisibility.fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ))
              (MvPolynomial.map (Int.castRingHom ℚ) (e j : MvPolynomial (Fin N × Fin N) ℤ)) /
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν)

def MuStd {N : ℕ} (ν : Fin N → ℕ) (μ : ℝ) : Prop :=
  ∃ (r : ℕ) (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)), 0 < r ∧
    μ = -Real.log ((stdGram ν e).det : ℝ) / r

def cNu {N : ℕ} (ν : Fin N → ℕ) : ℝ :=
  (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) / ∏ l, ((ν l).factorial : ℝ)

def HookBound : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ), Antitone ν →
    1 ≤ cNu ν ∧ cNu ν ≤ ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)

def StdSlopeLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (μ : ℝ), Antitone ν → MuStd ν μ →
    -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) ≤ μ

def ColSlopeEq (D : D7) : Prop :=
  ∀ u, ColVal D u → ∃ μs : D.what₂.Tau → ℝ, (∀ τ, MuStd ((D.fm u).lam 0 τ).natW (μs τ)) ∧
    ((D.fm u).lat 0).mu = -(∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) + ∑ τ, μs τ

def SlopeMaxC (D : D7) : Prop :=
  ∀ u, ColVal D u → ((D.fm u).lat 0).muMax ≤
    ∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
      Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem natWeight_cast_eq_sub_last {N : ℕ} (lam : DomWeight N) (hN : 0 < N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = (lam.w i : ℝ) - (lam.w ⟨N - 1, by omega⟩ : ℝ) := by
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i := lam.anti (Fin.le_def.mpr (by simp; omega))
  have h1 : ((lam.w i - lam.w ⟨N - 1, by omega⟩).toNat : ℤ) = lam.w i - lam.w ⟨N - 1, by omega⟩ :=
    Int.toNat_of_nonneg (by omega)
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos hN]
  have h2 : (((lam.w i - lam.w ⟨N - 1, by omega⟩).toNat : ℕ) : ℝ) =
      (((lam.w i - lam.w ⟨N - 1, by omega⟩).toNat : ℤ) : ℝ) := by norm_cast
  rw [h2, h1]
  push_cast
  ring

theorem antitone_natWeight {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j h
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti h) _)

theorem columnCount_pos (D : D7) : 0 < D.R.k := by
  have := D.R.m_add_three_le_k
  omega

theorem rank_zero_pos (D : D7) : 0 < D.R.N 0 := by
  simp only [Formalism.BasicNotions.Ranks.N, zero_mul, add_zero]
  exact columnCount_pos D

theorem weight_eq_lamCol (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin (D.R.N 0)) :
    ((((D.fm u).lam 0 τ).w i : ℤ) : ℝ) = ((lamCol D u τ i : ℚ) : ℝ) := by
  have h := b_lam_eq D u 0 (Nat.zero_le _) τ i
  have hi : i.1 < D.R.k := lt_of_lt_of_eq i.2 (Ranks.N_zero _)
  unfold lamLiftN at h
  rw [if_pos hi] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_intCast] at h'
  exact h'

theorem natWeight_eq_lamCol_sub (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (l : Fin (D.R.N 0)) :
    (((((D.fm u).lam 0 τ).natW l : ℕ)) : ℝ) = (lamCol D u τ l : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ) := by
  have hN := rank_zero_pos D
  rw [natWeight_cast_eq_sub_last _ hN l, weight_eq_lamCol, weight_eq_lamCol]
  simp [Formalism.BasicNotions.Ranks.N]

theorem sum_natWeight_eq_colAbsShifted (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (∑ l : Fin (D.R.N 0), (((((D.fm u).lam 0 τ).natW l : ℕ)) : ℝ)) = colAbsP D u τ := by
  simp only [natWeight_eq_lamCol_sub]
  rw [Fin.sum_univ_eq_sum_range (fun i => (lamCol D u τ i : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ)) (D.R.N 0)]
  have hN : D.R.N 0 = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
  rw [hN, colAbsP]

theorem natWeight_zero_eq_firstSpread (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (((((D.fm u).lam 0 τ).natW ⟨0, rank_zero_pos D⟩ : ℕ)) : ℝ) = firstColumnSpread D u τ := by
  rw [natWeight_eq_lamCol_sub]
  rfl

theorem colAbsShifted_nonneg (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 ≤ colAbsP D u τ := by
  rw [← sum_natWeight_eq_colAbsShifted]
  positivity

theorem firstColumnSpread_nonneg (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 ≤ firstColumnSpread D u τ := by
  rw [← natWeight_zero_eq_firstSpread]
  positivity

theorem log_hookConst_le_sq_mul_log (hH : HookBound) (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Real.log (cNu ((D.fm u).lam 0 τ).natW) ≤ (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) := by
  have hN := rank_zero_pos D
  have hanti := antitone_natWeight ((D.fm u).lam 0 τ)
  obtain ⟨h1, h2⟩ := hH (D.R.N 0) hN _ hanti
  rw [natWeight_zero_eq_firstSpread] at h2
  have hNk : (D.R.N 0 : ℝ) = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
  rw [hNk] at h2
  have hpos : 0 < cNu ((D.fm u).lam 0 τ).natW := by linarith
  have hb : 1 ≤ firstColumnSpread D u τ + D.R.k := by
    have h3 := firstColumnSpread_nonneg D u τ
    have h4 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast columnCount_pos D
    linarith
  have hlog0 : 0 ≤ Real.log (firstColumnSpread D u τ + D.R.k) := Real.log_nonneg hb
  have hN' : D.R.N 0 = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
  calc Real.log (cNu ((D.fm u).lam 0 τ).natW)
      ≤ Real.log ((firstColumnSpread D u τ + D.R.k) ^ (D.R.N 0 * (D.R.N 0 - 1) / 2)) := Real.log_le_log hpos h2
    _ = ((D.R.N 0 * (D.R.N 0 - 1) / 2 : ℕ) : ℝ) * Real.log (firstColumnSpread D u τ + D.R.k) := Real.log_pow _ _
    _ ≤ (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) := by
        apply mul_le_mul_of_nonneg_right _ hlog0
        rw [hN']
        have h5 : D.R.k * (D.R.k - 1) / 2 ≤ D.R.k ^ 2 := by
          calc D.R.k * (D.R.k - 1) / 2 ≤ D.R.k * (D.R.k - 1) := Nat.div_le_self _ _
            _ ≤ D.R.k * D.R.k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ = D.R.k ^ 2 := (sq _).symm
        exact_mod_cast h5

theorem slopeLowerOpen_of_std_hook (hS : StdSlopeLow) (hH : HookBound) (D : D7) (hC : ColSlopeEq D) : SlopeLowerOpenPart D := by
  intro u hu
  obtain ⟨μs, hμ, heq⟩ := hC u hu
  unfold SlopeLow
  rw [heq]
  have hτ : ∀ τ, -(colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k)) ≤
      μs τ := by
    intro τ
    have h1 := hS (D.R.N 0) _ (μs τ) (antitone_natWeight _) (hμ τ)
    rw [sum_natWeight_eq_colAbsShifted] at h1
    have hNk : (D.R.N 0 : ℝ) = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
    rw [hNk] at h1
    have h2 := log_hookConst_le_sq_mul_log hH D u τ
    linarith
  have hsum : -∑ τ, (colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k)) ≤
      ∑ τ, μs τ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun τ _ => hτ τ)
  linarith

theorem slopeMaxOpen_of_hook_two_le_v (hH : HookBound) (D : D7) (hv : 2 ≤ D.host.v) (hR : SlopeMaxC D) : SlopeMaxOpenPart D 4 := by
  intro u hu
  refine (hR u hu).trans (Finset.sum_le_sum (fun τ _ => ?_))
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
  have hv0 : (0 : ℝ) < D.host.v := by linarith
  have hlog : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) ≤ 4 * Real.log (D.R.k * D.host.v) := by
    rw [show (4 : ℝ) * Real.log (D.R.k * D.host.v) = Real.log (((D.R.k : ℝ) * D.host.v) ^ 4) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have h4 : (4 : ℝ) ≤ D.host.v ^ 2 := by nlinarith
    calc 4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2 ≤ D.host.v ^ 2 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2 := by gcongr
      _ = ((D.R.k : ℝ) * D.host.v) ^ 4 := by ring
  have h1 := mul_le_mul_of_nonneg_left hlog (colAbsShifted_nonneg D u τ)
  have h2 := log_hookConst_le_sq_mul_log hH D u τ
  have hT : 0 ≤ Real.log (Tu D u) := Real.log_natCast_nonneg _
  have h3 : -(lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u) ≤
      |(lamCol D u τ (D.R.k - 1) : ℝ)| * Real.log (Tu D u) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hT
  nlinarith

theorem two_le_half_rootDiscr (D : D7) : 2 ≤ D.host.v := by
  unfold Host.v
  have h := (factRd D.R D.host).2.2
  have h0 : 0 ≤ D.host.rdE := le_trans (by positivity) (factRd D.R D.host).1
  have he : 2 ≤ D.R.e := D.host.two_le_e
  have hn : 4 ≤ D.R.n := by
    have h1 : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.two_pow_dvd_ord
    have h2 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
    show 4 ≤ D.R.ord
    omega
  have hf : (8 : ℝ) ≤ D.R.f := by
    have : 8 ≤ D.R.f := by
      show 8 ≤ 2 * D.R.n
      omega
    exact_mod_cast this
  have h4 : (4 : ℝ) ≤ D.host.rdE := by
    by_contra hlt
    push Not at hlt
    nlinarith
  linarith

theorem slopeMaxOpen_of_hook (hH : HookBound) (D : D7) (hR : SlopeMaxC D) : SlopeMaxOpenPart D 4 := slopeMaxOpen_of_hook_two_le_v hH D (two_le_half_rootDiscr D) hR

theorem familySlopeLowerOpen_of_std (hS : StdSlopeLow) (hH : HookBound) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : fam0 Fm ColSlopeEq) : FamilySlopeLowerOpenPart Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hx1 i => slopeLowerOpen_of_std_hook hS hH _ (hx0 x hx hx1 i)⟩

theorem familySlopeMaxOpen_of_hook_v (hH : HookBound) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : fam0 Fm fun D => 2 ≤ D.host.v ∧ SlopeMaxC D) : FamilySlopeMaxOpenPart Fm 4 := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hx1 i => slopeMaxOpen_of_hook_two_le_v hH _ (hx0 x hx hx1 i).1 (hx0 x hx hx1 i).2⟩

theorem familySlopeMaxOpen_of_hook (hH : HookBound) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : fam0 Fm SlopeMaxC) : FamilySlopeMaxOpenPart Fm 4 := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hx1 i => slopeMaxOpen_of_hook hH _ (hx0 x hx hx1 i)⟩

section ShortVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ShortAt (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) : Prop :=
  (∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) ∧ LinearIndependent D.host.E y ∧
    ∀ a, ((Algebra.trace ℚ D.host.E ((D.sp.X 0).hT (y a) (y a)) : ℚ) : ℝ) / (2 * D.R.f) ≤
      (D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2

def ShortDual (D : D7) : Prop :=
  ∀ u (c : (D.mem u).C.cls 0), LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) →
    ∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, ShortAt D u c y

def SlopeMaxGiven (D : D7) : Prop :=
  ∀ u, ColVal D u → (∀ c, ∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, ShortAt D u c y) →
    ((D.fm u).lat 0).muMax ≤
      ∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxC_of (D : D7) (hS : ShortDual D) (hG : SlopeMaxGiven D) : SlopeMaxC D := fun u hu => hG u hu (fun c => hS u c (hu.latT c))

theorem slope_max_open_four_of_hookBound (hH : HookBound) (D : D7) (hS : ShortDual D) (hG : SlopeMaxGiven D) : SlopeMaxOpenPart D 4 := slopeMaxOpen_of_hook hH D (slopeMaxC_of D hS hG)

theorem family_slope_max_open_four_of_hookBound (hH : HookBound) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : fam0 Fm fun D => ShortDual D ∧ SlopeMaxGiven D) : FamilySlopeMaxOpenPart Fm 4 := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hx1 i => slope_max_open_four_of_hookBound hH _ (hx0 x hx hx1 i).1 (hx0 x hx hx1 i).2⟩

end ShortVec

end B23b

end Formalism.MainNotions.flipTwoThree
