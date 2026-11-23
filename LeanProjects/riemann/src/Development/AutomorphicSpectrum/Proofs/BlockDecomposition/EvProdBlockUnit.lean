import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.MPDict.HermRep

section Main
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ev_resU {U W : (MP ℤ m n).Opens} (e : W ≤ U) {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (u : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((res e u : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ U (u : Γ(MP ℤ m n, U)) y :=
  CxPts.ev_res e h _

theorem ev_prod_zpow {W : (MP ℤ m n).Opens} {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) {ι : Type} [Fintype ι] (b : ι → Γ(MP ℤ m n, W)ˣ) (e : ι → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, b k ^ e k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (CxPts.ev (mpStr ℤ m n) σ₀ W (b k : Γ(MP ℤ m n, W)) y) ^ e k := by
  have key : ∀ x : Γ(MP ℤ m n, W)ˣ, CxPts.ev (mpStr ℤ m n) σ₀ W (x : Γ(MP ℤ m n, W)) y =
      ((Units.map (evHom h).toMonoidHom x : ℂˣ) : ℂ) := fun x => ev_eq h _
  rw [key, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem ev_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (k : Fin (m + 1)) (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W (blockUnit i j h : Γ(MP ℤ m n, W)) y = z ⟨k, j⟩ / z ⟨k, i⟩ := by
  have hi : W ≤ blockChart n k i := h.trans ((prB n k).preimage_mono inf_le_left)
  have e1 : (blockUnit i j h : Γ(MP ℤ m n, W)) = pullRatio (prB n k) W i hi j :=
    appLE_ratioOn (φ := prB n k) (i := i) (j := j)
      (inf_le_left : chart ℤ (n k) i ⊓ chart ℤ (n k) j ≤ chart ℤ (n k) i) h
  rw [e1, ← resG_pullRatio (W := blockChart n k i) (hi := le_rfl) hi, CxPts.ev_res hi hW]
  exact (hy k i).2 j (ptsIn_mono hi hW)

theorem ev_prod_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (a : Fin (m + 1) → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, blockUnit (c k) (c' k) (h k) ^ a k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k := by
  rw [ev_prod_zpow hW]
  exact Finset.prod_congr rfl fun k _ => by rw [ev_blockUnit hy k _ _ (h k) hW]

theorem isUnder_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (l : Fin (m + 1) → ℂ) (hl : ∀ k, l k ≠ 0) : IsUnder y (fun p => l p.1 * z p) := by
  intro k i
  obtain ⟨h1, h2⟩ := hy k i
  refine ⟨h1.trans ⟨fun h => mul_ne_zero (hl k) h, fun h => right_ne_zero_of_mul h⟩, fun j hj => ?_⟩
  rw [h2 j hj, mul_div_mul_left _ _ (hl k)]

theorem isUnder_of_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (l : Fin (m + 1) → ℂ)
    (hl : ∀ k, l k ≠ 0) (hy : IsUnder y (fun p => l p.1 * z p)) : IsUnder y z := by
  have := isUnder_smul hy (fun k => (l k)⁻¹) fun k => inv_ne_zero (hl k)
  simpa only [inv_mul_cancel_left₀ (hl _)] using this

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

def hval (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) (i : M.B.ι) (c : ∀ k, Bk n k) : ℝ :=
  (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) *
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)

theorem hval_chart (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ)
    (i j : M.B.ι) (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hj : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U j ⊓ mchart c)) :
    hval M a u y z i c = hval M a u y z j c := by
  rw [mem_ptsIn_inf] at hi hj
  have hij : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ M.B.U j ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hi.1, hj.1⟩, hi.2⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j ⊓ mchart c)ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h1 i j c)
  simp only [Units.val_mul, ev_mul, ev_resU _ hij] at e
  have hg : gv (mpStr ℤ m n) σ₀ M.B i j y ≠ 0 := gv_ne_zero hi.1 hj.1
  have hpos : 0 < ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := norm_pos_iff.2 hg
  have ht := (M.φ σ₀).trans i j y hi.1 hj.1
  unfold hval
  rw [e, ht, norm_mul]
  change _ = _ * (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ * _) * _
  have ex : Real.exp (((M.φ σ₀).φ i y - Real.log (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ ^ 2)) / 2) =
      Real.exp ((M.φ σ₀).φ i y / 2) / ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := by
    rw [Real.log_pow, sub_div, Real.exp_sub]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ / 2 =
      Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ by push_cast; ring, Real.exp_log hpos]
  rw [ex]
  field_simp

theorem hval_multi (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k)) {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (hy : IsUnder y z) (i : M.B.ι) (c c' : ∀ k, Bk n k)
    (hc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hc' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c')) :
    hval M a u y z i c = hval M a u y z i c' := by
  rw [mem_ptsIn_inf] at hc hc'
  have hcc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ (mchart c ⊓ mchart c')) :=
    mem_ptsIn_inf.2 ⟨hc.1, mem_ptsIn_inf.2 ⟨hc.2, hc'.2⟩⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ (mchart c ⊓ mchart c'))ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h2 i c c')
  simp only [Units.val_mul, ev_mul, ev_resU _ hcc] at e
  rw [ev_prod_blockUnit hy c c' (fun k => (fun _ hx => ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
    M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))) hcc a] at e
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) hc.2)
  unfold hval
  rw [e, norm_mul, norm_prod]
  have hk : ∀ k, ‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖ = ‖z ⟨k, c' k⟩‖ ^ a k := by
    intro k
    rw [norm_zpow, norm_div, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hz k)))]
  calc (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) * (‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * ∏ k, ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖) * Real.exp ((M.φ σ₀).φ i y / 2)
      = (∏ k, (‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖)) * ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * Real.exp ((M.φ σ₀).φ i y / 2) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp only [hk]

end Main

section Metric
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def ptC (y : CxPts (mpStr ℤ m n) σ₀) : ∀ k, Bk n k := fun k => ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k

theorem mem_ptC (y : CxPts (mpStr ℤ m n) σ₀) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptC y)) :=
  mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k)

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

theorem mem_pick_ptC (y : CxPts (mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (pick M.isLB y) ⊓ mchart (ptC y)) :=
  mem_ptsIn_inf.2 ⟨mem_pick M.isLB y, mem_ptC y⟩

open Classical in

def hOf (z : (Σ k, Bk n k) → ℂ) : ℝ :=
  if hz : ∃ y, IsUnder y z then hval M a u hz.choose z (pick M.isLB hz.choose) (ptC hz.choose) else 0

theorem hOf_eq (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y')
    {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι) (c : ∀ k, Bk n k)
    (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : hOf M a u z = hval M a u y z i c := by
  have hz : ∃ y, IsUnder y z := ⟨y, hy⟩
  rw [hOf, dif_pos hz, uniq z _ _ hz.choose_spec hy]
  have h0 := mem_pick_ptC M y
  rw [mem_ptsIn_inf] at h0 hi
  rw [hval_chart M a u h1 z (pick M.isLB y) i (ptC y) (mem_ptsIn_inf.2 h0) (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩),
    hval_multi M a u h2 hy i (ptC y) c (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩) (mem_ptsIn_inf.2 hi)]

theorem hval_pos {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι)
    (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : 0 < hval M a u y z i c := by
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k =>
    ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) (mem_ptsIn_inf.1 hi).2)
  refine mul_pos (mul_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hz k)) _)
    (norm_pos_iff.2 (ev_ne_zero hi (u i c).isUnit))) (Real.exp_pos _)

theorem hval_smul {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ) (l : Fin (m + 1) → ℂ) (i : M.B.ι)
    (c : ∀ k, Bk n k) : hval M a u y (fun p => l p.1 * z p) i c = (∏ k, ‖l k‖ ^ a k) * hval M a u y z i c := by
  unfold hval
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

def lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    Geo.HermLine (Bk n) where
  a := a
  h := hOf M a u
  pos z hz := by
    obtain ⟨y, hy⟩ := ex z hz
    rw [hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y)]
    exact hval_pos M a u hy _ _ (mem_pick_ptC M y)
  smul l z hl := by
    by_cases hz : ∃ y, IsUnder y z
    · obtain ⟨y, hy⟩ := hz
      rw [hOf_eq M a u h1 h2 uniq (isUnder_smul hy l hl) _ _ (mem_pick_ptC M y),
        hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y), hval_smul]
    · have hz' : ¬ ∃ y, IsUnder y (fun p => l p.1 * z p) := fun ⟨y, hy⟩ => hz ⟨y, isUnder_of_smul l hl hy⟩
      rw [hOf, dif_neg hz', hOf, dif_neg hz, mul_zero]

theorem isHermRep_lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    IsHermRep M (lineOf M a u h1 h2 ex uniq) :=
  ⟨u, h1, h2, fun i c _ _ hy hi => hOf_eq M a u h1 h2 uniq hy i c hi⟩

end Metric

theorem exists_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), IsTwB M →
    ∃ A : Geo.HermLine (Bk n), IsHermRep M A := by
  intro m n M hM
  obtain ⟨c, t, ⟨hw⟩⟩ := hM
  obtain ⟨u, h1, h2⟩ := GlobalTheory.CompanionTheory.MPDict.TwUnits.exists_units m n M.B c t M.isLB hw
  exact ⟨_, isHermRep_lineOf M _ u h1 h2 (GlobalTheory.CompanionTheory.MPDict.UnderExists.exists_isUnder m n) (GlobalTheory.CompanionTheory.MPDict.isUnder_unique m n)⟩

end GlobalTheory.CompanionTheory.MPDict.HermRep
