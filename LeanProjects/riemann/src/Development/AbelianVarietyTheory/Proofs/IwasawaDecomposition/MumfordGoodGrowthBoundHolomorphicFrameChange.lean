import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.FrameChange

variable {K : Type} [Fintype K]

def EntryLe (M : Matrix K K ℂ) (x : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ x

variable {M N : Matrix K K ℂ} {x y : ℝ}

theorem EntryLe.mono (h : EntryLe M x) (hxy : x ≤ y) : EntryLe M y := fun i j => (h i j).trans hxy

theorem EntryLe.add (h : EntryLe M x) (h' : EntryLe N y) : EntryLe (M + N) (x + y) :=
  fun i j => (norm_add_le _ _).trans (add_le_add (h i j) (h' i j))

theorem EntryLe.sub (h : EntryLe M x) (h' : EntryLe N y) : EntryLe (M - N) (x + y) :=
  fun i j => (norm_sub_le _ _).trans (add_le_add (h i j) (h' i j))

theorem EntryLe.neg (h : EntryLe M x) : EntryLe (-M) x := fun i j => by
  simpa using h i j

theorem EntryLe.mul (hx : 0 ≤ x) (h : EntryLe M x) (h' : EntryLe N y) :
    EntryLe (M * N) (Fintype.card K * x * y) := by
  intro i j
  rw [mul_apply]
  calc ‖∑ l, M i l * N l j‖ ≤ ∑ l, ‖M i l * N l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : K, x * y := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]; exact mul_le_mul (h i l) (h' l j) (norm_nonneg _) hx
    _ = Fintype.card K * x * y := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem EntryLe.smul {w : ℝ} (hw : 0 ≤ w) (h : EntryLe M x) : EntryLe ((w : ℂ) • M) (w * x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (h i j) hw

theorem entryLe_smul_of {w c : ℝ} (hw : 0 ≤ w) (h : ∀ i j, ‖M i j‖ * w ≤ c) :
    EntryLe ((w : ℂ) • M) c := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, mul_comm]
  exact h i j

theorem EntryLe.of_smul {w : ℝ} (hw : 0 ≤ w) (h : EntryLe ((w : ℂ) • M) x) (i j : K) :
    ‖M i j‖ * w ≤ x := by
  have := h i j
  rwa [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw,
    mul_comm] at this

theorem EntryLe.transpose (h : EntryLe M x) : EntryLe Mᵀ x := fun i j => h j i

theorem EntryLe.conjTranspose (h : EntryLe M x) : EntryLe Mᴴ x := fun i j => by
  rw [conjTranspose_apply, norm_star]; exact h j i

theorem EntryLe.norm_det_le [DecidableEq K] (h : EntryLe M x) :
    ‖M.det‖ ≤ (Fintype.card K).factorial * x ^ Fintype.card K := by
  rw [det_apply]
  calc ‖∑ σ : Equiv.Perm K, Equiv.Perm.sign σ • ∏ i, M (σ i) i‖
      ≤ ∑ σ : Equiv.Perm K, ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm K, x ^ Fintype.card K := Finset.sum_le_sum fun σ _ => by
        have hs : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ∏ i, ‖M (σ i) i‖ := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ, norm_prod]
        rw [hs]
        calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : K, x :=
              Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => h _ _
          _ = x ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem mdel_conn_changeFrame : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (G₀ A : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → GlobalTheory.HermFrame.MContDiffAt 2 A v → IsUnit (A v).det → (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar A u η = 0) → ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V n, GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) u ζ) v ξ = (A v)⁻¹ * (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn G₀ u ζ) v ξ * A v + GlobalTheory.HermFrame.conn G₀ v ζ * GlobalTheory.HermFrame.mdel A v ξ + GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel A u ζ) v ξ) - (A v)⁻¹ * GlobalTheory.HermFrame.mdel A v ξ * (A v)⁻¹ * (GlobalTheory.HermFrame.conn G₀ v ζ * A v + GlobalTheory.HermFrame.mdel A v ζ) := by
  intro n K _ _ G₀ A v hG hGu hA hAu hA0 ξ ζ
  have hA1 : GlobalTheory.HermFrame.MContDiffAt 1 A v := hA.of_le one_le_two
  have hc : GlobalTheory.HermFrame.MContDiffAt 1 (fun x => GlobalTheory.HermFrame.conn G₀ x ζ) v :=
    hG.conn hGu (by norm_num) ζ
  have hd : GlobalTheory.HermFrame.MContDiffAt 1 (fun x => GlobalTheory.HermFrame.mdel A x ζ) v := hA.mdel (by norm_num) ζ
  have he : (fun x => GlobalTheory.HermFrame.conn (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) x ζ) =ᶠ[nhds v]
      fun x => (A x)⁻¹ * (GlobalTheory.HermFrame.conn G₀ x ζ * A x + GlobalTheory.HermFrame.mdel A x ζ) := by
    filter_upwards [hG.eventually_two, hG.eventually_isUnit hGu, hA.eventually_two,
      hA.eventually_isUnit hAu, hA0] with x h1 h2 h3 h4 h5
    exact GlobalTheory.HermFrame.conn_changeFrame (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 h5 ζ
  rw [GlobalTheory.HermFrame.mdel_congr he, GlobalTheory.HermFrame.mdel_mul (hA1.inv hAu) ((hc.mul hA1).add hd),
    GlobalTheory.HermFrame.mdel_inv hA1 hAu, GlobalTheory.HermFrame.mdel_add (hc.mul hA1) hd,
    GlobalTheory.HermFrame.mdel_mul hc hA1]
  noncomm_ring

theorem entryLe_antisymm_del : ∀ (K : Type) [Fintype K] (X A Ta Tb Dab Dba dAa dAb ddAab ddAba : Matrix K K ℂ) (wa wb b c : ℝ), 0 ≤ wa → wa ≤ 1 → 0 ≤ wb → wb ≤ 1 → 0 ≤ b → 0 ≤ c → GlobalTheory.GoodMetric.FrameChange.EntryLe X b → GlobalTheory.GoodMetric.FrameChange.EntryLe A b → GlobalTheory.GoodMetric.FrameChange.EntryLe dAa b → GlobalTheory.GoodMetric.FrameChange.EntryLe dAb b → GlobalTheory.GoodMetric.FrameChange.EntryLe ddAab b → GlobalTheory.GoodMetric.FrameChange.EntryLe ddAba b → GlobalTheory.GoodMetric.FrameChange.EntryLe ((wa : ℂ) • Ta) c → GlobalTheory.GoodMetric.FrameChange.EntryLe ((wb : ℂ) • Tb) c → GlobalTheory.GoodMetric.FrameChange.EntryLe (((wa * wb : ℝ) : ℂ) • (Dab - Dba)) c → GlobalTheory.GoodMetric.FrameChange.EntryLe (((wa * wb : ℝ) : ℂ) • ((X * (Dab * A + Tb * dAa + ddAab) - X * dAa * X * (Tb * A + dAb)) - (X * (Dba * A + Ta * dAb + ddAba) - X * dAb * X * (Ta * A + dAa)))) (3 * (Fintype.card K : ℝ) ^ 2 * b ^ 2 * c + 2 * (Fintype.card K : ℝ) ^ 4 * b ^ 4 * c + 2 * (Fintype.card K : ℝ) ^ 3 * b ^ 4 + 2 * (Fintype.card K : ℝ) * b ^ 2) := by
  intro K _ X A Ta Tb Dab Dba dAa dAb ddAab ddAba wa wb b c hwa0 hwa1 hwb0 hwb1 hb hc hX hA hdAa hdAb hddab hddba hTa hTb hD
  set k : ℝ := (Fintype.card K : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have e : (((wa * wb : ℝ) : ℂ) • ((X * (Dab * A + Tb * dAa + ddAab) - X * dAa * X * (Tb * A + dAb)) -
      (X * (Dba * A + Ta * dAb + ddAba) - X * dAb * X * (Ta * A + dAa)))) =
      X * (((wa * wb : ℝ) : ℂ) • (Dab - Dba)) * A + X * ((wb : ℂ) • Tb) * ((wa : ℂ) • dAa)
        - X * ((wa : ℂ) • Ta) * ((wb : ℂ) • dAb)
        - X * ((wa : ℂ) • dAa) * X * ((wb : ℂ) • Tb) * A + X * ((wb : ℂ) • dAb) * X * ((wa : ℂ) • Ta) * A
        - ((wa * wb : ℝ) : ℂ) • (X * dAa * X * dAb) + ((wa * wb : ℝ) : ℂ) • (X * dAb * X * dAa)
        + ((wa * wb : ℝ) : ℂ) • (X * (ddAab - ddAba)) := by
    push_cast
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, smul_add, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, mul_comm (wb : ℂ) (wa : ℂ)]
    abel
  have hwa : wa * b ≤ b := by nlinarith
  have hwb : wb * b ≤ b := by nlinarith
  have hw0 : 0 ≤ wa * wb := mul_nonneg hwa0 hwb0
  have hw1 : wa * wb ≤ 1 := by nlinarith
  have hkb : 0 ≤ k * b * b := by positivity
  have t1 : GlobalTheory.GoodMetric.FrameChange.EntryLe (X * (((wa * wb : ℝ) : ℂ) • (Dab - Dba)) * A) (k ^ 2 * b ^ 2 * c) :=
    ((hX.mul hb hD).mul (by positivity) hA).mono (le_of_eq (by ring))
  have t2 : GlobalTheory.GoodMetric.FrameChange.EntryLe (X * ((wb : ℂ) • Tb) * ((wa : ℂ) • dAa)) (k ^ 2 * b ^ 2 * c) :=
    ((hX.mul hb hTb).mul (by positivity) (hdAa.smul hwa0)).mono (by
      have := mul_le_mul_of_nonneg_left hwa (by positivity : 0 ≤ k * (k * b * c))
      nlinarith)
  have t3 : GlobalTheory.GoodMetric.FrameChange.EntryLe (X * ((wa : ℂ) • Ta) * ((wb : ℂ) • dAb)) (k ^ 2 * b ^ 2 * c) :=
    ((hX.mul hb hTa).mul (by positivity) (hdAb.smul hwb0)).mono (by
      have := mul_le_mul_of_nonneg_left hwb (by positivity : 0 ≤ k * (k * b * c))
      nlinarith)
  have t4 : GlobalTheory.GoodMetric.FrameChange.EntryLe (X * ((wa : ℂ) • dAa) * X * ((wb : ℂ) • Tb) * A) (k ^ 4 * b ^ 4 * c) := by
    have h := ((((hX.mul hb (hdAa.smul hwa0)).mul (by positivity) hX).mul (by positivity) hTb).mul
      (by positivity) hA)
    refine h.mono ?_
    have := mul_le_mul_of_nonneg_left hwa (by positivity : 0 ≤ k ^ 4 * b ^ 2 * c)
    nlinarith
  have t5 : GlobalTheory.GoodMetric.FrameChange.EntryLe (X * ((wb : ℂ) • dAb) * X * ((wa : ℂ) • Ta) * A) (k ^ 4 * b ^ 4 * c) := by
    have h := ((((hX.mul hb (hdAb.smul hwb0)).mul (by positivity) hX).mul (by positivity) hTa).mul
      (by positivity) hA)
    refine h.mono ?_
    have := mul_le_mul_of_nonneg_left hwb (by positivity : 0 ≤ k ^ 4 * b ^ 2 * c)
    nlinarith
  have t6 : GlobalTheory.GoodMetric.FrameChange.EntryLe (((wa * wb : ℝ) : ℂ) • (X * dAa * X * dAb)) (k ^ 3 * b ^ 4) := by
    refine ((((hX.mul hb hdAa).mul (by positivity) hX).mul (by positivity) hdAb).smul hw0).mono ?_
    have := mul_le_mul_of_nonneg_right hw1 (by positivity : 0 ≤ k ^ 3 * b ^ 4)
    nlinarith
  have t7 : GlobalTheory.GoodMetric.FrameChange.EntryLe (((wa * wb : ℝ) : ℂ) • (X * dAb * X * dAa)) (k ^ 3 * b ^ 4) := by
    refine ((((hX.mul hb hdAb).mul (by positivity) hX).mul (by positivity) hdAa).smul hw0).mono ?_
    have := mul_le_mul_of_nonneg_right hw1 (by positivity : 0 ≤ k ^ 3 * b ^ 4)
    nlinarith
  have t8 : GlobalTheory.GoodMetric.FrameChange.EntryLe (((wa * wb : ℝ) : ℂ) • (X * (ddAab - ddAba))) (2 * k * b ^ 2) := by
    refine ((hX.mul hb (hddab.sub hddba)).smul hw0).mono ?_
    have := mul_le_mul_of_nonneg_right hw1 (by positivity : 0 ≤ 2 * k * b ^ 2)
    nlinarith
  rw [e]
  refine (((((((t1.add t2).sub t3).sub t4).add t5).sub t6).add t7).add t8).mono (le_of_eq ?_)
  ring

theorem poinWt_mem {n : ℕ} (S : Finset (Fin n)) {v : ReciprocityTheory.L2DbarEstimates.V n} (hv : ‖v‖ < 1) (a : Fin n) :
    0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 := by
  unfold poinWt
  split_ifs with ha
  · have h1 : ‖v a‖ < 1 := (PiLp.norm_apply_le v a).trans_lt hv
    refine ⟨by positivity, ?_⟩
    rcases (norm_nonneg (v a)).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have := Real.abs_log_mul_self_lt ‖v a‖ h0 h1.le
      rw [abs_mul, abs_of_pos h0] at this
      linarith
  · exact ⟨zero_le_one, le_rfl⟩

theorem goodBound_changeFrame : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (B : ℝ), ∃ c' : ℝ, ∀ (G₀ P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), ‖v‖ < 1 → (G₀ v).det ≠ 0 → (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) → (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) → (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) → IsUnit (P v).det → (∀ i k, ‖P v i k‖ ≤ B) → (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) → (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → GlobalTheory.GoodMetric.GoodBound S c N G₀ v → (P v * G₀ v * (P v)ᴴ).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => (P u * G₀ u * (P u)ᴴ) i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c' N (fun u => P u * G₀ u * (P u)ᴴ) v := by
  intro n K _ _ S c N B
  set k : ℝ := (Fintype.card K : ℝ) with hk
  set b : ℝ := |B| with hb
  set D : ℝ := ((Fintype.card K).factorial : ℝ) * b ^ Fintype.card K with hD
  refine ⟨D ^ 2 * c + k ^ 2 * b ^ 2 * c + (k ^ 2 * b ^ 2 * c + k * b ^ 2) + k ^ 2 * b ^ 2 * c +
    (3 * k ^ 2 * b ^ 2 * c + 2 * k ^ 4 * b ^ 4 * c + 2 * k ^ 3 * b ^ 4 + 2 * k * b ^ 2), ?_⟩
  intro G₀ P v hv hdet hG hP hhol hPu hPb hPib hdPb hddPb hgb
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hD0 : 0 ≤ D := by positivity
  set s : ℝ := ∑ a ∈ S, |Real.log ‖v a‖| with hs
  have hs0 : 0 ≤ s ^ N := pow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _
  have hcpos : 0 < c := by
    have h1 := hgb.det
    have h2 : 0 < ‖(G₀ v).det‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hdet)
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hs0]
  have hc0 := hcpos.le

  set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ := fun u => (P u)ᵀ with hA
  have hGA : (fun u => P u * G₀ u * (P u)ᴴ) = fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ := rfl
  have hG2 : GlobalTheory.HermFrame.MContDiffAt 2 G₀ v := hG
  have hP2 : GlobalTheory.HermFrame.MContDiffAt 2 P v := hP
  have hA2 : GlobalTheory.HermFrame.MContDiffAt 2 A v := hP2.transpose
  have hG1 : GlobalTheory.HermFrame.MContDiffAt 1 G₀ v := hG2.of_le one_le_two
  have hA1 : GlobalTheory.HermFrame.MContDiffAt 1 A v := hA2.of_le one_le_two
  have hGu : IsUnit (G₀ v).det := hdet.isUnit
  have hAu : IsUnit (A v).det := by simpa [hA, det_transpose] using hPu
  have hAhol : ∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar A u η = 0 :=
    hhol.mono fun u hu η => by
      rw [hA, GlobalTheory.HermFrame.mdbar_transpose, hu η, transpose_zero]

  have eB : ∀ (M : Matrix K K ℂ), (∀ i j, ‖M i j‖ ≤ B) → EntryLe M b :=
    fun M h i j => (h i j).trans (le_abs_self B)
  have hX : EntryLe (A v)⁻¹ b := by
    intro i j
    have := (eB _ hPib) j i
    show ‖((P v)ᵀ)⁻¹ i j‖ ≤ b
    rw [← transpose_nonsing_inv]; exact this
  have hAb : EntryLe (A v) b := (eB _ hPb).transpose
  have hdA : ∀ a, EntryLe (GlobalTheory.HermFrame.mdel A v (coordVec a)) b := fun a =>
    (eB _ (hdPb a)).transpose
  have hddA : ∀ a b', EntryLe (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel A u (coordVec b')) v
      (coordVec a)) b := fun a b' => (eB _ (hddPb a b')).transpose
  have hw := poinWt_mem S hv
  have hconn : ∀ ξ, GlobalTheory.HermFrame.conn (fun u => P u * G₀ u * (P u)ᴴ) v ξ =
      (A v)⁻¹ * (GlobalTheory.HermFrame.conn G₀ v ξ * A v + GlobalTheory.HermFrame.mdel A v ξ) := fun ξ => by
    rw [hGA]
    exact GlobalTheory.HermFrame.conn_changeFrame hG1 hGu hA1 hAu hAhol.self_of_nhds ξ
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hPu.ne_zero hdet) (star_ne_zero.2 hPu.ne_zero)
  · exact (hP2.mul hG2).mul hP2.conjTranspose
  constructor
  ·
    intro i j
    have hG0e : EntryLe (G₀ v) (c * s ^ N) := hgb.entry
    have h1 := ((eB _ hPb).mul hb0 hG0e).mul (by positivity) (eB _ hPb).conjTranspose
    refine (h1 i j).trans ?_
    have e : k * (k * b * (c * s ^ N)) * b = (k ^ 2 * b ^ 2 * c) * s ^ N := by ring
    rw [← hk, e]
    refine mul_le_mul_of_nonneg_right ?_ hs0
    have : 0 ≤ D ^ 2 * c := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c + k * b ^ 2 := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c := by positivity
    have : 0 ≤ 3 * k ^ 2 * b ^ 2 * c + 2 * k ^ 4 * b ^ 4 * c + 2 * k ^ 3 * b ^ 4 + 2 * k * b ^ 2 := by
      positivity
    linarith
  ·
    have hPi : ‖(P v).det‖⁻¹ ≤ D := by
      have h1 := (eB _ hPib).norm_det_le
      rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv] at h1
      exact h1
    have e : ‖(P v * G₀ v * (P v)ᴴ).det‖⁻¹ = ‖(P v).det‖⁻¹ ^ 2 * ‖(G₀ v).det‖⁻¹ := by
      rw [det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star]
      rw [mul_inv, mul_inv]; ring
    rw [e]
    calc ‖(P v).det‖⁻¹ ^ 2 * ‖(G₀ v).det‖⁻¹ ≤ D ^ 2 * (c * s ^ N) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hPi 2) hgb.det (by positivity) (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hs0
        have : 0 ≤ k ^ 2 * b ^ 2 * c + k * b ^ 2 := by positivity
        have : 0 ≤ k ^ 2 * b ^ 2 * c := by positivity
        have : 0 ≤ 3 * k ^ 2 * b ^ 2 * c + 2 * k ^ 4 * b ^ 4 * c + 2 * k ^ 3 * b ^ 4 + 2 * k * b ^ 2 := by
          positivity
        linarith
  ·
    intro a i j
    set w := poinWt S v a
    have hT : EntryLe ((w : ℂ) • GlobalTheory.HermFrame.conn G₀ v (coordVec a)) c :=
      entryLe_smul_of (hw a).1 (hgb.form a)
    have e : (w : ℂ) • GlobalTheory.HermFrame.conn (fun u => P u * G₀ u * (P u)ᴴ) v (coordVec a) =
        (A v)⁻¹ * (((w : ℂ) • GlobalTheory.HermFrame.conn G₀ v (coordVec a)) * A v) +
          (w : ℂ) • ((A v)⁻¹ * GlobalTheory.HermFrame.mdel A v (coordVec a)) := by
      rw [hconn, Matrix.mul_add, smul_add, Matrix.smul_mul, Matrix.mul_smul]
    have h1 : EntryLe ((w : ℂ) • GlobalTheory.HermFrame.conn (fun u => P u * G₀ u * (P u)ᴴ) v (coordVec a))
        (k ^ 2 * b ^ 2 * c + k * b ^ 2) := by
      rw [e]
      refine ((hX.mul hb0 (hT.mul hc0 hAb)).add ((hX.mul hb0 (hdA a)).smul (hw a).1)).mono ?_
      rw [← hk]
      have : (w * (k * b * b)) ≤ k * b ^ 2 := by
        have := mul_le_mul_of_nonneg_right (hw a).2 (by positivity : 0 ≤ k * b * b)
        nlinarith
      nlinarith
    refine (h1.of_smul (hw a).1 i j).trans ?_
    have : 0 ≤ D ^ 2 * c := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c := by positivity
    have : 0 ≤ 3 * k ^ 2 * b ^ 2 * c + 2 * k ^ 4 * b ^ 4 * c + 2 * k ^ 3 * b ^ 4 + 2 * k * b ^ 2 := by
      positivity
    linarith
  ·
    intro a b' i j
    set w := poinWt S v a * poinWt S v b'
    have hw0 : 0 ≤ w := mul_nonneg (hw a).1 (hw b').1
    have hF : EntryLe ((w : ℂ) • GlobalTheory.HermFrame.curv G₀ v (coordVec a) (coordVec b')) c :=
      entryLe_smul_of hw0 (hgb.dbar a b')
    have e : GlobalTheory.HermFrame.curv (fun u => P u * G₀ u * (P u)ᴴ) v (coordVec a) (coordVec b') =
        (A v)⁻¹ * GlobalTheory.HermFrame.curv G₀ v (coordVec a) (coordVec b') * A v := by
      rw [hGA]
      exact GlobalTheory.HermFrame.curv_changeFrame hG2 hGu hA2 hAu hAhol _ _
    have h1 : EntryLe ((w : ℂ) • GlobalTheory.HermFrame.curv (fun u => P u * G₀ u * (P u)ᴴ) v (coordVec a)
        (coordVec b')) (k ^ 2 * b ^ 2 * c) := by
      rw [e, Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul]
      refine (hX.mul hb0 (hF.mul hc0 hAb)).mono (le_of_eq ?_)
      rw [← hk]; ring
    refine (h1.of_smul hw0 i j).trans ?_
    have : 0 ≤ k ^ 2 * b ^ 2 * c := by positivity
    have : 0 ≤ D ^ 2 * c := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c + k * b ^ 2 := by positivity
    have : 0 ≤ 3 * k ^ 2 * b ^ 2 * c + 2 * k ^ 4 * b ^ 4 * c + 2 * k ^ 3 * b ^ 4 + 2 * k * b ^ 2 := by
      positivity
    linarith
  ·
    intro a b' i j
    set wa := poinWt S v a
    set wb := poinWt S v b'
    have hw0 : 0 ≤ wa * wb := mul_nonneg (hw a).1 (hw b').1
    have e1 := mdel_conn_changeFrame n K G₀ A v hG2 hGu hA2 hAu hAhol (coordVec a) (coordVec b')
    have e2 := mdel_conn_changeFrame n K G₀ A v hG2 hGu hA2 hAu hAhol (coordVec b') (coordVec a)
    rw [← hGA] at e1 e2
    have h1 := entryLe_antisymm_del K (A v)⁻¹ (A v) (GlobalTheory.HermFrame.conn G₀ v (coordVec a))
      (GlobalTheory.HermFrame.conn G₀ v (coordVec b'))
      (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn G₀ u (coordVec b')) v (coordVec a))
      (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn G₀ u (coordVec a)) v (coordVec b'))
      (GlobalTheory.HermFrame.mdel A v (coordVec a)) (GlobalTheory.HermFrame.mdel A v (coordVec b'))
      (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel A u (coordVec b')) v (coordVec a))
      (GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel A u (coordVec a)) v (coordVec b'))
      wa wb b c (hw a).1 (hw a).2 (hw b').1 (hw b').2 hb0 hc0 hX hAb (hdA a) (hdA b') (hddA a b')
      (hddA b' a) (entryLe_smul_of (hw a).1 (hgb.form a)) (entryLe_smul_of (hw b').1 (hgb.form b'))
      (entryLe_smul_of hw0 (hgb.del a b'))
    rw [← e1, ← e2] at h1
    refine (h1.of_smul hw0 i j).trans ?_
    rw [← hk]
    have : 0 ≤ D ^ 2 * c := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c + k * b ^ 2 := by positivity
    have : 0 ≤ k ^ 2 * b ^ 2 * c := by positivity
    linarith

end GlobalTheory.GoodMetric.FrameChange
