import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

noncomputable section

namespace GlobalTheory.FrameNorm.UnitFr

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hermC_mul_left {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G (fun k => u k * α) v = α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermC_mul_right {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) (α : ℂ) :
    hermC τ G u (fun k => v k * α) = (starRingEnd ℂ) α * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul]
  ring

theorem col_mul_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℝ) (c : Fin r) :
    col (A * Matrix.diagonal fun a => (β a : ℂ)) c = fun k => col A c k * (β c : ℂ) := by
  funext k
  simp [col, Matrix.mul_diagonal]

theorem gram_mul_diag {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A : Matrix (Fin r) (Fin r) ℂ)
    (β : Fin r → ℝ) :
    gram τ G (A * Matrix.diagonal fun a => (β a : ℂ)) =
      Matrix.diagonal (fun a => (β a : ℂ)) * gram τ G A * Matrix.diagonal (fun a => (β a : ℂ)) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [gram, Matrix.of_apply, col_mul_diag, hermC_mul_left, hermC_mul_right, Complex.conj_ofReal]
  ring

theorem lminor_diag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (β : Fin r → ℂ) (i : Fin (r + 1)) :
    lminor (Matrix.diagonal β * M * Matrix.diagonal β) i =
      (∏ a : Fin i, β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 * lminor M i := by
  unfold lminor
  have e : (Matrix.diagonal β * M * Matrix.diagonal β).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) =
      Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) *
        M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) *
        Matrix.diagonal (fun a => β (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) := by
    ext a b
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

variable {r : ℕ} (X : Data E r)

def tq (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := ‖dmin X.Gm x τ a.succ / dmin X.Gm x τ a.castSucc‖

def bt (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin r) : ℝ := tq X x τ a ^ (-(1 : ℝ) / 2)

def unitB (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)

def unitF (x : Frame X.Ψ r) : Frame X.Ψ r := rmul x (unitB X x)

theorem mat_unitF (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (unitF X x) τ = mat x τ * Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) := rfl

theorem dmin_unitF (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (unitF X x) τ i =
      (((∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 : ℝ) : ℂ) * dmin X.Gm x τ i := by
  unfold dmin
  rw [mat_unitF, gram_mul_diag, lminor_diag]
  push_cast
  rfl

variable {X}

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have := (hx' τ).2 i
  rw [h, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

theorem tq_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < tq X x τ a :=
  norm_pos_iff.2 (div_ne_zero (dmin_ne hx τ _) (dmin_ne hx τ _))

theorem bt_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) : 0 < bt X x τ a :=
  Real.rpow_pos_of_pos (tq_pos hx τ a) _

theorem bt_sq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r) :
    bt X x τ a ^ 2 = (tq X x τ a)⁻¹ := by
  unfold bt
  rw [← Real.rpow_natCast, ← Real.rpow_mul (tq_pos hx τ a).le]
  norm_num
  exact Real.rpow_neg_one _

def gN (x : Frame X.Ψ r) (τ : X.Ψ) (m : ℕ) : ℝ := if h : m < r + 1 then ‖dmin X.Gm x τ ⟨m, h⟩‖ else 1

theorem gN_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (m : ℕ) : gN x τ m ≠ 0 := by
  unfold gN
  split_ifs with h
  · exact norm_ne_zero_iff.2 (dmin_ne hx τ _)
  · exact one_ne_zero

theorem gN_zero (x : Frame X.Ψ r) (τ : X.Ψ) : gN x τ 0 = 1 := by
  unfold gN
  rw [dif_pos (Nat.succ_pos r)]
  have : dmin X.Gm x τ ⟨0, Nat.succ_pos r⟩ = 1 := Matrix.det_fin_zero
  rw [this, norm_one]

theorem prod_gN {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (n : ℕ) :
    ∏ m ∈ Finset.range n, gN x τ m / gN x τ (m + 1) = gN x τ 0 / gN x τ n := by
  induction n with
  | zero => simp [div_self (gN_ne hx τ 0)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [gN_ne hx τ n, gN_ne hx τ (n + 1), gN_ne hx τ 0]

theorem tq_castLE {x : Frame X.Ψ r} (τ : X.Ψ) {i : ℕ} (hi : i ≤ r) (a : Fin i) :
    tq X x τ (Fin.castLE hi a) = gN x τ (a + 1) / gN x τ a := by
  unfold tq gN
  rw [dif_pos (by omega), dif_pos (by omega), norm_div]
  rfl

theorem norm_dmin_unitF {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (unitF X x) τ i‖ = 1 := by
  rw [dmin_unitF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← Finset.prod_pow]
  have h1 : ∀ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a) ^ 2 =
      gN x τ (a : ℕ) / gN x τ ((a : ℕ) + 1) := by
    intro a
    rw [bt_sq hx, tq_castLE, inv_div]
  simp_rw [h1]
  rw [Fin.prod_univ_eq_prod_range (fun m => gN x τ m / gN x τ (m + 1)), prod_gN hx, gN_zero]
  have h2 : gN x τ i = ‖dmin X.Gm x τ i‖ := by
    unfold gN
    rw [dif_pos i.isLt]
  rw [h2, div_mul_cancel₀ _ (norm_ne_zero_iff.2 (dmin_ne hx τ i))]

theorem unitB_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitB X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (Matrix.diagonal fun a => ((bt X x τ a : ℝ) : ℂ)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne'
  · show Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) a c = 0
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hca)

theorem unitF_mem (x : Frame X.Ψ r) (hx : x ∈ X.dom) : unitF X x ∈ X.dom := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_unitF, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hx' τ).1
      (Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (bt_pos hx τ a).ne')
  · rw [dmin_unitF, Complex.re_ofReal_mul]
    have hs : 0 < (∏ a : Fin i, bt X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) ^ 2 :=
      pow_pos (Finset.prod_pos fun a _ => bt_pos hx τ _) 2
    have := (hx' τ).2 i
    nlinarith

theorem pnorm_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) :
    X.pnorm la P (unitF X x) = X.pnorm la P x := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]
  rw [show unitF X x = rmul x (unitB X x) from rfl, hB _ (unitB_mem x hx), norm_mul, mul_comm]
  congr 1
  unfold bchar
  simp only [norm_prod, norm_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ‖(Matrix.diagonal (fun a => ((bt X x τ a : ℝ) : ℂ)) i i)‖ ^ la τ i = _
  rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_of_nonneg (bt_pos hx τ i).le]
  unfold bt
  rw [← Real.rpow_intCast, ← Real.rpow_mul (tq_pos hx τ i).le]
  unfold tq
  congr 1
  ring

theorem pnorm_eq_unitF (x : Frame X.Ψ r) (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : X.IsSec la P) : X.pnorm la P x = ‖P (unitF X x)‖ := by
  rw [← pnorm_unitF x hx la P (hP.2.1 x hx)]
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm (unitF X x) τ i.succ / dmin X.Gm (unitF X x) τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, norm_dmin_unitF hx, norm_dmin_unitF hx, div_one]
  simp_rw [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem lact_one' {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end GlobalTheory.FrameNorm.UnitFr

namespace GlobalTheory.FrameNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem exists_unitFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU
  have h3 := hU.2.2.1
  have h4 := hU.2.2.2.1
  clear hU
  let uf : ∀ k, (U.X k).dom → (U.X k).dom := fun k x => ⟨UnitFr.unitF (U.X k) x.1, UnitFr.unitF_mem x.1 x.2⟩
  have huf : ∀ k x, (uf k x).1 = FD.rmul x.1 (UnitFr.unitB (U.X k) x.1) := fun _ _ => rfl
  have hun : ∀ k x, IsUnitFr (U.X k) (uf k x).1 := fun k x τ i => UnitFr.norm_dmin_unitF x.2 τ i
  have hpn : ∀ k (x : (U.X k).dom) (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P →
      (U.X k).pnorm la P x.1 = ‖P (uf k x).1‖ := fun k x la P hP => UnitFr.pnorm_eq_unitF x.1 x.2 la P hP
  clear_value uf
  have key : ∀ k (x : (U.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k (uf k x)) (U.un k x) := by
    intro k x
    obtain ⟨t, ht⟩ := (h4 k k x (uf k x)).2
      ⟨1, (U.X k).Γ.one_mem, UnitFr.unitB (U.X k) x.1, UnitFr.unitB_mem x.1 x.2, by
        rw [UnitFr.lact_one', huf]⟩
    exact ⟨t⁻¹, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k (uf k x))
      (U.un k x)).2.2.2 t ht⟩
  refine ⟨fun k x => ⟨uf k x, hun k x, ⟨_, UnitFr.unitB_mem x.1 x.2, huf k x⟩, key k x, hpn k x⟩, fun y => ?_⟩
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨s, hs⟩ := key k x
  exact ⟨k, uf k x, t * s, hun k x,
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k (uf k x)) (U.un k x) y).2.2.1 s t hs ht⟩

end GlobalTheory.FrameNorm
