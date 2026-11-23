import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwLine

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mem_ptsIn_mchart {y : CxPts (mpStr ℤ m n) σ₀} {c : ∀ k, Bk n k} :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) ↔ ∀ k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := by
  rw [mem_ptsIn]
  exact ⟨fun h k => mem_ptsIn.2 (Set.mem_iInter.1 h k), fun h => Set.mem_iInter.2 fun k => mem_ptsIn.1 (h k)⟩

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn inf_le_left h]
  rfl

theorem ev_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z)
    {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      z ⟨k, j⟩ / z ⟨k, i⟩ := by
  have hW : W ≤ blockChart n k i := h.trans ((prB n k).preimage_mono inf_le_left)
  rw [val_blockUnit, ← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) hW,
    CxPts.ev_res hW hy]
  exact (hz k i).2 j (ptsIn_mono hW hy)

theorem IsUnder.smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z)
    {a : Fin (m + 1) → ℂ} (ha : ∀ k, a k ≠ 0) : IsUnder y fun p => a p.1 * z p := by
  intro k i
  refine ⟨?_, fun j hi => ?_⟩
  · rw [(hz k i).1]
    simp [ha k]
  · rw [(hz k i).2 j hi]
    exact (mul_div_mul_left _ _ (ha k)).symm

theorem norm_mul_exp_trans {g v : ℂ} (hg : g ≠ 0) (φ : ℝ) :
    ‖g * v‖ * Real.exp ((φ - Real.log (‖g‖ ^ 2)) / 2) = ‖v‖ * Real.exp (φ / 2) := by
  have hp : 0 < ‖g‖ := norm_pos_iff.2 hg
  have e : (φ - Real.log (‖g‖ ^ 2)) / 2 = φ / 2 - Real.log ‖g‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [e, Real.exp_sub, Real.exp_log hp, norm_mul]
  field_simp

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

def hVal (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) (i : M.B.ι) (c : ∀ k, Bk n k) : ℝ :=
  (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) *
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)

def FrameLaw : Prop := ∀ i j c,
  Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
    Semi.res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
      Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)

def MonoLaw : Prop := ∀ i c c',
  Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
      M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
    ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
      ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
        M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k

variable {M a u}

theorem hVal_frame (h : FrameLaw M u) {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ) {i j : M.B.ι}
    {c : ∀ k, Bk n k} (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i))
    (hj : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U j)) (hc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) :
    hVal M a u y z j c = hVal M a u y z i c := by
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ M.B.U j ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hi, hj⟩, hc⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j ⊓ mchart c)ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ (w : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j ⊓ mchart c)) y) (h i j c)
  simp only [Units.val_mul, CxPts.ev_mul] at e
  have e1 := CxPts.ev_res (p := mpStr ℤ m n) (σ := σ₀) (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) hW (u j c : Γ(MP ℤ m n, M.B.U j ⊓ mchart c))
  have e2 := CxPts.ev_res (p := mpStr ℤ m n) (σ := σ₀) (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) hW
    (M.B.g i j : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j))
  have e3 := CxPts.ev_res (p := mpStr ℤ m n) (σ := σ₀) (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) hW (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c))
  have e' : CxPts.ev (mpStr ℤ m n) σ₀ _ (u j c : Γ(MP ℤ m n, M.B.U j ⊓ mchart c)) y =
      GlobalTheory.CxPts.gv (mpStr ℤ m n) σ₀ M.B i j y * CxPts.ev (mpStr ℤ m n) σ₀ _ (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y := by
    rw [← e1, GlobalTheory.CxPts.gv, ← e2, ← e3]
    exact e
  simp only [hVal]
  rw [e', (M.φ σ₀).trans i j y hi hj, mul_assoc, mul_assoc, norm_mul_exp_trans (gv_ne_zero hi hj)]

theorem hVal_mono (h : MonoLaw M a u) {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z)
    {i : M.B.ι} {c c' : ∀ k, Bk n k} (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i))
    (hc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) (hc' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c')) :
    hVal M a u y z i c = hVal M a u y z i c' := by
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ (mchart c ⊓ mchart c')) :=
    mem_ptsIn_inf.2 ⟨hi, mem_ptsIn_inf.2 ⟨hc, hc'⟩⟩
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (mem_ptsIn_mchart.1 hc k)
  have hz0' : ∀ k, z ⟨k, c' k⟩ ≠ 0 := fun k => (hz k (c' k)).1.1 (mem_ptsIn_mchart.1 hc' k)
  let ρ : Γ(MP ℤ m n, M.B.U i ⊓ (mchart c ⊓ mchart c'))ˣ →* ℂˣ := Units.map (evHom hW : _ →+* ℂ)
  have hρ : ∀ w, ((ρ w : ℂˣ) : ℂ) = CxPts.ev (mpStr ℤ m n) σ₀ _ (w : Γ(MP ℤ m n, M.B.U i ⊓ (mchart c ⊓ mchart c'))) y :=
    fun w => (CxPts.ev_eq hW _).symm
  have e := congrArg (fun w => ((ρ w : ℂˣ) : ℂ)) (h i c c')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, hρ] at e
  have e1 := CxPts.ev_res (p := mpStr ℤ m n) (σ := σ₀) (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) hW (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c))
  have e2 := CxPts.ev_res (p := mpStr ℤ m n) (σ := σ₀) (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
      M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') hW (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c'))
  have e' : CxPts.ev (mpStr ℤ m n) σ₀ _ (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ _ (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y *
        ∏ k, (z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k := by
    rw [← e1, ← e2]
    refine Eq.trans e ?_
    congr 1
    exact Finset.prod_congr rfl fun k _ => congrArg (· ^ a k) (ev_blockUnit hz (c k) (c' k) _ hW)
  simp only [hVal]
  rw [e', norm_mul, norm_prod]
  have e3 : (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) * ∏ k, ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖ = ∏ k, ‖z ⟨k, c' k⟩‖ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have := norm_pos_iff.2 (hz0 k)
    rw [norm_zpow, norm_div, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ this.ne')]
  rw [← e3]
  ring

theorem hVal_eq (h₁ : FrameLaw M u) (h₂ : MonoLaw M a u) {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (hz : IsUnder y z) {i j : M.B.ι} {c c' : ∀ k, Bk n k}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (h' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U j ⊓ mchart c')) :
    hVal M a u y z i c = hVal M a u y z j c' := by
  have a1 := mem_ptsIn_inf.1 h
  have a2 := mem_ptsIn_inf.1 h'
  rw [hVal_mono h₂ hz a1.1 a1.2 a2.2]
  exact (hVal_frame h₁ z a1.1 a2.1 a2.2).symm

theorem hVal_pos {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z) {i : M.B.ι}
    {c : ∀ k, Bk n k} (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) :
    0 < hVal M a u y z i c := by
  have hc := (mem_ptsIn_inf.1 h).2
  refine mul_pos (mul_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 ?_) _) (norm_pos_iff.2 ?_))
    (Real.exp_pos _)
  · exact (hz k (c k)).1.1 (mem_ptsIn_mchart.1 hc k)
  · exact ev_ne_zero h (u i c).isUnit

theorem hVal_smul {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ) (i : M.B.ι)
    (c : ∀ k, Bk n k) (b : Fin (m + 1) → ℂ) :
    hVal M a u y (fun p => b p.1 * z p) i c = (∏ k, ‖b k‖ ^ a k) * hVal M a u y z i c := by
  have e : (∏ k, ‖b k * z ⟨k, c k⟩‖ ^ a k) = (∏ k, ‖b k‖ ^ a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [norm_mul, mul_zpow]
  simp only [hVal]
  rw [e]
  ring

theorem exists_data (z : (Σ k, Bk n k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ (y : CxPts (mpStr ℤ m n) σ₀) (i : M.B.ι) (c : ∀ k, Bk n k), IsUnder y z ∧
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) := by
  obtain ⟨y, hy, -⟩ := Under.existsUnique_isUnder m n z hz
  choose c hc using hz
  exact ⟨y, pick M.isLB y, c, hy, mem_ptsIn_inf.2 ⟨mem_pick _ y,
    mem_ptsIn_mchart.2 fun k => (hy k (c k)).1.2 (hc k)⟩⟩

theorem exists_hermLine (h₁ : FrameLaw M u) (h₂ : MonoLaw M a u) :
    ∃ A : Geo.HermLine (Bk n), IsHermRep M A ∧ A.a = a := by
  classical
  have key : ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ r : ℝ, 0 < r ∧
      ∀ (y : CxPts (mpStr ℤ m n) σ₀) (i : M.B.ι) (c : ∀ k, Bk n k), IsUnder y z →
        y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) → r = hVal M a u y z i c := by
    intro z hz
    obtain ⟨y, i, c, hy, hm⟩ := exists_data (M := M) z hz
    refine ⟨hVal M a u y z i c, hVal_pos hy hm, fun y' j c' hy' hm' => ?_⟩
    obtain rfl : y' = y := (Under.existsUnique_isUnder m n z hz).unique hy' hy
    exact hVal_eq h₁ h₂ hy hm hm'
  let H : ((Σ k, Bk n k) → ℂ) → ℝ := fun z =>
    if hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then (key z hz).choose else 0
  have Hpos : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < H z := fun z hz => by
    simp only [H, dif_pos hz]
    exact (key z hz).choose_spec.1
  have Hval : ∀ z (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀) (i : M.B.ι) (c : ∀ k, Bk n k),
      IsUnder y z → y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) → H z = hVal M a u y z i c :=
    fun z hz y i c hy hm => by
      simp only [H, dif_pos hz]
      exact (key z hz).choose_spec.2 y i c hy hm
  refine ⟨⟨a, H, Hpos, fun b z hb => ?_⟩, ⟨u, h₁, h₂, fun i c y z hy hm => ?_⟩, rfl⟩
  · by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · have hz' : ∀ k, ∃ i, (fun p : Σ k, Bk n k => b p.1 * z p) ⟨k, i⟩ ≠ 0 := fun k => by
        obtain ⟨i, hi⟩ := hz k
        exact ⟨i, mul_ne_zero (hb k) hi⟩
      obtain ⟨y, i, c, hy, hm⟩ := exists_data (M := M) z hz
      rw [Hval z hz y i c hy hm, Hval _ hz' y i c (IsUnder.smul hy hb) hm, hVal_smul]
    · have hz' : ¬ ∀ k, ∃ i, (fun p : Σ k, Bk n k => b p.1 * z p) ⟨k, i⟩ ≠ 0 := fun h => hz fun k => by
        obtain ⟨i, hi⟩ := h k
        exact ⟨i, right_ne_zero_of_mul hi⟩
      simp only [H, dif_neg hz, dif_neg hz', mul_zero]
  · have hc := (mem_ptsIn_inf.1 hm).2
    exact Hval z (fun k => ⟨c k, (hy k (c k)).1.1 (mem_ptsIn_mchart.1 hc k)⟩) y i c hy hm

end GlobalTheory.CompanionTheory.MPDict.TwLine

namespace GlobalTheory.CompanionTheory.MPDict.TwLine

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    simp

variable {M : HermLB (mpStr ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso M.B (twB m n b t)) (i : M.B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso M.B (twB m n b t)) (i : M.B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ M.B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ M.B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frameLaw_uOf {w : LB.Iso M.B (twB m n b t)} (hw : w.IsGen) : FrameLaw M (uOf w) := by
  intro i j c
  have hc : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ M.B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ M.B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem monoLaw_uOf {w : LB.Iso M.B (twB m n b t)} (hw : w.IsGen) :
    MonoLaw M (Pi.single b.succ 1 + t • Pi.single 0 1) (uOf w) := by
  intro i c c'
  have hc : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ M.B.U i) (M.B.g i i) = 1 :=
    Units.ext (LB.resG_g_self M.isLB i _)
  have hi : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ M.B.U i := le_inf hU inf_le_left
  have hi' : M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ M.B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (M.B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_hermLine_of_twB : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ),
    Nonempty (LBIso M.B (twB m n c t)) →
      ∃ A : Geo.HermLine (Bk n), IsHermRep M A ∧ A.a = Pi.single c.succ 1 + t • Pi.single 0 1 := by
  rintro m n M b t ⟨⟨w, hw⟩⟩
  exact exists_hermLine (frameLaw_uOf hw) (monoLaw_uOf hw)

end GlobalTheory.CompanionTheory.MPDict.TwLine
