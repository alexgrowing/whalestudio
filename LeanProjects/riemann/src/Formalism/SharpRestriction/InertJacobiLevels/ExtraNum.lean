import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

theorem facProd_succ (n : ℕ) : facProd (n + 1) = (n.superFactorial : ℝ) := by
  unfold facProd
  rw [Finset.prod_range_succ', Nat.factorial_zero, Nat.cast_one, mul_one, ← Nat.prod_range_factorial_succ]
  push_cast
  rfl

theorem sf_pos (n : ℕ) : 0 < n.superFactorial := by
  rw [← Nat.prod_range_factorial_succ]
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

theorem dimV_nat {N : ℕ} (x : Fin N → ℝ) (z : Fin N → ℤ) (c : ℝ) (hx : ∀ i, x i = z i + c) (hz : StrictAnti z) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = dimV x := by
  cases N with
  | zero => exact ⟨1, one_pos, by simp [dimV, vand, facProd]⟩
  | succ n =>
    obtain ⟨q, hq⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => -z i)
    rw [Matrix.det_vandermonde] at hq
    have hpos : (0 : ℤ) < ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (-z j - -z i) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => by
        have := hz (Finset.mem_Ioi.1 hj)
        omega
    have hsf : (0 : ℤ) < (n.superFactorial : ℤ) := by exact_mod_cast sf_pos n
    have hq0 : 0 < q := by
      rw [hq] at hpos
      exact (pos_iff_pos_of_mul_pos hpos).1 hsf
    have hV : vand x = ((∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (-z j - -z i) : ℤ) : ℝ) := by
      unfold vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Finset.filter_lt_eq_Ioi]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hx a, hx b]
      ring
    refine ⟨q.toNat, by omega, ?_⟩
    unfold dimV
    rw [hV, hq, facProd_succ]
    have h1 : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
      have : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0.le
      exact_mod_cast this
    have h2 : ((n.superFactorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (sf_pos n).ne'
    rw [h1]
    push_cast
    field_simp

theorem strictAnti_of_step {N : ℕ} (f : Fin N → ℚ)
    (h : ∀ (i : ℕ) (h1 : i + 1 < N), f ⟨i + 1, h1⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a + 1 ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a hb
  | succ n hn ih => exact (h n hb).trans (ih (by omega) (by show a < n; omega))

theorem hc_u_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.u :=
  strictAnti_of_step _ fun i h1 =>
    (P.v_gt_u ⟨i, by omega⟩).trans (P.u_gt_v ⟨i, by omega⟩)

theorem dimV_hc {R : Ranks} (P : HCParam R) : ∃ n : ℕ, 0 < n ∧ (n : ℝ) = dimV (fun i => ((P.u i : ℚ) : ℝ)) := by
  choose z hz using P.u_half
  refine dimV_nat _ z (1 / 2) (fun i => by rw [hz i]; push_cast; ring) fun a b hab => ?_
  have := hc_u_strictAnti P hab
  rw [hz a, hz b] at this
  have h2 : (z b : ℚ) < z a := by linarith
  exact_mod_cast h2

def massH {R : Ranks} (H : Host R) (M : ℕ) : ℝ :=
  letI := H.cmStar
  Formalism.HermitianLatticesTheory.mass (stdForm H.E M) (stdLat H.E M)

def duStarH {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) : ℝ :=
  massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) *
    ∏ ρ, dimV (fun i => (((hc ρ).u i : ℚ) : ℝ))

theorem duStarU_eq (D : D7) (u : D.what₂.Word) : duStarU D u = duStarH D.host (D.hcW u) := rfl

def GSplit {R : Ranks} (H : Host R) : Prop :=
  (∀ i, (placesOver H.E (H.g i)).ncard = Module.finrank ℚ H.E) ∧ ∀ i, 2 * R.f * R.k < H.g i - 1

def MassIntegral : Prop :=
  ∀ (R : Ranks) (H : Host R), GSplit H → ∃ N : ℕ, 0 < N ∧
    (N : ℝ) = massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f)

theorem exists_duStarH (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : ∃ N : ℕ, 0 < N ∧ (N : ℝ) = duStarH H hc := by
  obtain ⟨N0, h0, h1⟩ := hM R H hH
  choose n hn hn' using fun ρ => dimV_hc (hc ρ)
  refine ⟨N0 * ∏ ρ, n ρ, Nat.mul_pos h0 (Finset.prod_pos fun ρ _ => hn ρ), ?_⟩
  unfold duStarH
  rw [← h1]
  push_cast
  congr 1
  exact Finset.prod_congr rfl fun ρ _ => hn' ρ

def duNat (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : ℕ :=
  (exists_duStarH hM H hH hc).choose

theorem duNat_pos (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : 0 < duNat hM H hH hc := (exists_duStarH hM H hH hc).choose_spec.1

theorem duNat_eq (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : (duNat hM H hH hc : ℝ) = duStarH H hc := (exists_duStarH hM H hH hc).choose_spec.2

theorem duStar_def_iff (D : D7) (u : D.what₂.Word) :
    (((D.mem u).A.duStar : ℕ) : ℝ) = duStarU D u ↔ (((D.mem u).A.duStar : ℕ) : ℝ) = duStarH D.host (D.hcW u) := Iff.rfl

theorem isRowLev_one (k rS n : ℕ) (F : Type) [Zero F] [One F] [DecidableEq (Fin n)] :
    IsRowLev k rS (1 : Matrix (Fin n) (Fin n) F) := by
  refine ⟨fun i j h => Matrix.one_apply_ne ?_, fun i => Matrix.one_apply_eq i,
    fun i j _ h => Matrix.one_apply_ne (ne_of_gt h), fun i j _ h _ => Matrix.one_apply_ne h⟩
  rintro rfl
  exact lt_irrefl _ h

theorem idxRowLoc_pos (g k m : ℕ) [NeZero g] : 0 < idxRowLoc g k m := by
  unfold idxRowLoc idxLoc
  have : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} :=
    ⟨⟨1, by rw [Units.val_one]; exact isRowLev_one _ _ _ _⟩⟩
  have h1 : 0 < Nat.card (GL (Fin (k + m - 1)) (ZMod g)) := Nat.card_pos
  have h2 : 0 < Nat.card {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := Nat.card_pos
  positivity

def idxSigR (R : Ranks) (g : Fin 2 → ℕ) : ℝ := idxRowLoc (g 0) R.k R.m ^ R.f * idxRowLoc (g 1) R.k R.m ^ R.f

theorem idxSigR_pos (R : Ranks) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) : 0 < idxSigR R g := by
  have := fun i => NeZero.mk (hg i).ne_zero
  have h0 := idxRowLoc_pos (g 0) R.k R.m
  have h1 := idxRowLoc_pos (g 1) R.k R.m
  unfold idxSigR
  positivity

def volFor (R : Ranks) (g : Fin 2 → ℕ) {Tau : Type} [Fintype Tau] (dsig : Tau → ℝ) (Dst : ℝ) : ℝ :=
  Dst / (idxSigR R g * ∏ ρ, dsig ρ)

theorem volFor_pos (R : Ranks) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) {Tau : Type} [Fintype Tau] (dsig : Tau → ℝ)
    (hd : ∀ ρ, 0 < dsig ρ) (Dst : ℝ) (hD : 0 < Dst) : 0 < volFor R g dsig Dst :=
  div_pos hD (mul_pos (idxSigR_pos R g hg) (Finset.prod_pos fun ρ _ => hd ρ))

theorem dstar_def_of_vol (D : D7)
    (h : letI := D.host.cmStar; D.vol (D.sp.Y 0) = volFor D.R D.host.g D.dsig D.what₂.Dstar) :
    D.what₂.Dstar = DstarD D := by
  have h1 : 0 < idxSigR D.R D.host.g := idxSigR_pos _ _ D.host.g_prime
  have h2 : 0 < ∏ ρ, D.dsig ρ := Finset.prod_pos fun ρ _ => D.dsig_pos ρ
  show D.what₂.Dstar = volY0 D * idxSigR D.R D.host.g * ∏ ρ, D.dsig ρ
  unfold volY0
  rw [h, volFor]
  field_simp

end Formalism.MainNotions.Inhab

end
