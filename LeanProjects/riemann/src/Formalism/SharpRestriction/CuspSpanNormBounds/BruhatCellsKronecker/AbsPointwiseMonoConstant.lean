import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge

theorem cell_G_pos (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {γ : MatKR D.R.k D.R.rS}
    {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) (hz : inWb D.R.k D.R.rS z) (hz' : inWb D.R.k D.R.rS z')
    (hT : 0 < Tz D.R.k D.R.rS z) (hT' : 0 < Tz D.R.k D.R.rS z') : 0 < Gf D.R.k D.R.rS z z' γ :=
  lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ h.1) (Ne.symm h.2.2)

theorem mem_scanl_take (xs : List ℕ) : ∀ (a q : ℕ), a + (xs.take q).sum ∈ xs.scanl (· + ·) a := by
  induction xs with
  | nil => intro a q; simp
  | cons x xs ih =>
    intro a q
    cases q with
    | zero => simp [List.scanl_cons]
    | succ q =>
      have := ih (a + x) q
      rw [List.scanl_cons, List.take_succ_cons, List.sum_cons, List.mem_cons]
      right
      rwa [add_assoc] at this

theorem mem_blockEnds_of_take {i : ℕ} (p : Point ℂ i) (q l : ℕ) (h1 : 1 ≤ l)
    (hl : l = ((p.1.map Prod.snd).take q).sum) : l ∈ ptBlockEnds p := by
  have h := mem_scanl_take (p.1.map Prod.snd) 0 q
  rw [zero_add, ← hl] at h
  unfold ptBlockEnds
  cases hxs : p.1.map Prod.snd with
  | nil =>
    rw [hxs] at hl
    simp at hl
    omega
  | cons x xs =>
    rw [hxs, List.scanl_cons, List.mem_cons] at h
    rw [List.scanl_cons, List.tail_cons]
    rcases h with h | h
    · omega
    · exact h

theorem cell_normSq (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {γ : MatKR D.R.k D.R.rS}
    {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    Complex.normSq (DminN z z' γ l) = Complex.normSq (leadMinor (ptMat p) l hl) := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h.2.1
  have e : DminN z z' γ l = leadMinor (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ) l hl := by
    unfold DminN
    rw [dif_pos (Nat.lt_succ_of_le hl)]
    rfl
  rw [e, ← normSq_leadMinor_ZhatO, hZ, leadMinor_cell L (ptMat p) U hL hU l hl]

theorem cell_mem_blockEnds (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {γ : MatKR D.R.k D.R.rS}
    {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) (l : ℕ) (h1 : 1 ≤ l) (hl : l ≤ D.R.rS + 1)
    (hne : DminN z z' γ l ≠ 0) : l ∈ ptBlockEnds p := by
  have h2 : leadMinor (ptMat p) l hl ≠ 0 := by
    intro h0
    have := cell_normSq D h l hl
    rw [h0, map_zero] at this
    exact hne (Complex.normSq_eq_zero.1 this)
  have e : leadMinor (ptMat p) l hl =
      Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (Formalism.MainNotions.BesselShellMomentBounds.toComp p) (Formalism.MainNotions.BesselShellMomentBounds.toT p)) l := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.ptMat_eq]
    exact Formalism.MainNotions.BesselShellMomentBounds.leadMinorK_eq _ _ _
  by_contra hcon
  apply h2
  rw [e]
  apply Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish ℂ _ _ _ l hl
  intro q hq
  exact hcon (mem_blockEnds_of_take p q l h1 hq)

theorem cell_last_mem {r : ℕ} (p : Point ℂ (r + 1)) : r + 1 ∈ ptBlockEnds p := by
  apply mem_blockEnds_of_take p (p.1.map Prod.snd).length (r + 1) (by omega)
  rw [List.take_length]
  exact p.2.2.symm

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge

theorem take_of_mem_scanl (xs : List ℕ) : ∀ (a y : ℕ), y ∈ xs.scanl (· + ·) a → ∃ q, y = a + (xs.take q).sum := by
  induction xs with
  | nil => intro a y h; simp at h; exact ⟨0, by simp [h]⟩
  | cons x xs ih =>
    intro a y h
    rw [List.scanl_cons, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨q, hq⟩ := ih _ _ h
      exact ⟨q + 1, by rw [hq, List.take_succ_cons, List.sum_cons, add_assoc]⟩

theorem take_of_mem_blockEnds {i : ℕ} (p : Point ℂ i) (l : ℕ) (h : l ∈ ptBlockEnds p) :
    ∃ q, l = ((p.1.map Prod.snd).take q).sum := by
  obtain ⟨q, hq⟩ := take_of_mem_scanl (p.1.map Prod.snd) 0 l (List.mem_of_mem_tail h)
  exact ⟨q, by rw [hq, zero_add]⟩

theorem blockEnd_le {i : ℕ} (p : Point ℂ i) (l : ℕ) (h : l ∈ ptBlockEnds p) : l ≤ i := by
  obtain ⟨q, rfl⟩ := take_of_mem_blockEnds p l h
  exact (Formalism.MainNotions.BesselShellMomentBounds.toComp p).sizeUpTo_le q

theorem leadMinor_blockEnd_ne {i : ℕ} (p : Point ℂ i) (l : ℕ) (h : l ∈ ptBlockEnds p) (hl : l ≤ i) :
    leadMinor (ptMat p) l hl ≠ 0 := by
  obtain ⟨q, rfl⟩ := take_of_mem_blockEnds p l h
  have e : leadMinor (ptMat p) ((p.1.map Prod.snd).take q).sum hl =
      Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (Formalism.MainNotions.BesselShellMomentBounds.toComp p) (Formalism.MainNotions.BesselShellMomentBounds.toT p))
        ((Formalism.MainNotions.BesselShellMomentBounds.toComp p).sizeUpTo q) := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.ptMat_eq]
    exact Formalism.MainNotions.BesselShellMomentBounds.leadMinorK_eq _ _ _
  rw [e, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue]
  refine Finset.prod_ne_zero_iff.2 (fun a _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ?_))
  exact Formalism.MainNotions.BesselShellMomentBounds.toT_ne p a

theorem cell_ne_of_mem (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {γ : MatKR D.R.k D.R.rS}
    {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) (l : ℕ) (hm : l ∈ ptBlockEnds p) : DminN z z' γ l ≠ 0 := by
  intro h0
  have hl := blockEnd_le p l hm
  have := cell_normSq D h l hl
  rw [h0, map_zero] at this
  exact leadMinor_blockEnd_ne p l hm hl (Complex.normSq_eq_zero.1 this.symm)

theorem one_le_max_inv {x : ℝ} (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod_map_le (l : List ℕ) (f g : ℕ → ℝ) (h : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ g x) :
    0 ≤ (l.map f).prod ∧ (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg h1.1 h2.1, mul_le_mul h1.2 h2.2 h2.1 (le_trans h1.1 h1.2)⟩

theorem one_le_list_prod_map (l : List ℕ) (f : ℕ → ℝ) (h : ∀ x ∈ l, 1 ≤ f x) : 1 ≤ (l.map f).prod := by
  have := (list_prod_map_le l (fun _ => 1) f (fun x hx => ⟨zero_le_one, h x hx⟩)).2
  simpa using this

theorem one_le_foldr_max (l : List ℝ) : 1 ≤ l.foldr max 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons]; exact le_max_of_le_right ih

section Loss

variable {k r : ℕ} (b : ℝ) (m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1))

theorem one_le_lossP (hb : 1 ≤ b) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ lossP b C m z z' γ p := by
  unfold lossP
  apply Real.one_le_rpow
  · have h1 : 1 ≤ b ^ (C * (m : ℝ)) := Real.one_le_rpow hb (by positivity)
    have h2 := one_le_foldr_max ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    nlinarith
  · positivity

theorem lossP_mono (hb : 1 ≤ b) {C C₂ : ℝ} (hC : 0 ≤ C) (h : C ≤ C₂) :
    lossP b C m z z' γ p ≤ lossP b C₂ m z z' γ p := by
  unfold lossP
  have h2 := one_le_foldr_max ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
  have h1 : 1 ≤ b ^ (C * (m : ℝ)) := Real.one_le_rpow hb (by positivity)
  have h3 : b ^ (C * (m : ℝ)) ≤ b ^ (C₂ * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right h (by positivity))
  set Fm := ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹).foldr max 1 with hF
  have h4 : b ^ (C * (m : ℝ)) * Fm ≤ b ^ (C₂ * (m : ℝ)) * Fm := mul_le_mul_of_nonneg_right h3 (by linarith)
  have h5 : 1 ≤ b ^ (C₂ * (m : ℝ)) * Fm := by nlinarith
  calc (b ^ (C * (m : ℝ)) * Fm) ^ (C * (r : ℝ) ^ 3) ≤ (b ^ (C₂ * (m : ℝ)) * Fm) ^ (C * (r : ℝ) ^ 3) :=
        Real.rpow_le_rpow (by nlinarith) h4 (by positivity)
    _ ≤ (b ^ (C₂ * (m : ℝ)) * Fm) ^ (C₂ * (r : ℝ) ^ 3) :=
        Real.rpow_le_rpow_of_exponent_le h5 (mul_le_mul_of_nonneg_right h (by positivity))

theorem one_le_lossV (hb : 1 ≤ b) {C : ℝ} (hC : 0 ≤ C) (hG : 0 < Gf k r z z' γ)
    (hD : ∀ l ∈ ptBlockEnds p, DminN z z' γ l ≠ 0) : 1 ≤ lossV b C m z z' γ p := by
  unfold lossV
  have h1 : 1 ≤ b ^ (C * (m : ℝ) ^ 4) := Real.one_le_rpow hb (by positivity)
  have h2 : 1 ≤ (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹) ^ (C * (m : ℝ) ^ 2) :=
    Real.one_le_rpow (one_le_max_inv hG) (by positivity)
  have h3 : 1 ≤ ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C * (m : ℝ))).prod :=
    one_le_list_prod_map _ _ (fun l hl =>
      Real.one_le_rpow (one_le_max_inv (norm_pos_iff.2 (hD l hl))) (by positivity))
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by linarith)) h3 zero_le_one (by positivity)

theorem lossV_mono (hb : 1 ≤ b) {C C₂ : ℝ} (h : C ≤ C₂) (hG : 0 < Gf k r z z' γ)
    (hD : ∀ l ∈ ptBlockEnds p, DminN z z' γ l ≠ 0) : lossV b C m z z' γ p ≤ lossV b C₂ m z z' γ p := by
  unfold lossV
  have hb0 : 0 < b := by linarith
  have h1 : b ^ (C * (m : ℝ) ^ 4) ≤ b ^ (C₂ * (m : ℝ) ^ 4) :=
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right h (by positivity))
  have h2 : (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹) ^ (C * (m : ℝ) ^ 2) ≤
      (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹) ^ (C₂ * (m : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_max_inv hG) (mul_le_mul_of_nonneg_right h (by positivity))
  have h3 := list_prod_map_le (ptBlockEnds p)
    (fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C * (m : ℝ)))
    (fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C₂ * (m : ℝ)))
    (fun l hl => ⟨Real.rpow_nonneg (le_trans zero_le_one (one_le_max_inv (norm_pos_iff.2 (hD l hl)))) _,
      Real.rpow_le_rpow_of_exponent_le (one_le_max_inv (norm_pos_iff.2 (hD l hl)))
        (mul_le_mul_of_nonneg_right h (by positivity))⟩)
  have hG1 : 0 ≤ max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹ := le_trans zero_le_one (one_le_max_inv hG)
  exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hG1 _) (Real.rpow_nonneg hb0.le _)) h3.2 h3.1
    (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hG1 _))

end Loss

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

theorem hadamard_inequality_packet : VanishingOnXAndXPlusBranching.adm7 := LatticeGluingRadicals.hadamard_section

theorem one_le_b {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (le_trans zero_le_one large₂.sc.one_lt_alt.le) _

theorem abs_pointwise_mono_constant (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 A C1 C C₂ : ℝ} (hC : 0 ≤ C) (h : C ≤ C₂)
    (H : VanishingOnXAndXPlusBranching.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C) : VanishingOnXAndXPlusBranching.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C₂ := by
  intro τ w w' hTT θ hθ W hW S hS hdeg γ p hp θ' hθ' νR hν hH hD
  have h0 := H τ w w' hTT θ hθ W hW S hS hdeg γ p hp θ' hθ' νR hν hH hD
  refine le_trans h0 ?_
  have hv : 0 < D.host.v := lt_of_lt_of_le one_pos hH.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hP := lossP_mono large₂.sc.b D.R.m W.z W.z' γ p (one_le_b large₂) hC h
  have hP0 : 0 ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p :=
    le_trans zero_le_one (one_le_lossP large₂.sc.b D.R.m W.z W.z' γ p (one_le_b large₂) hC)
  have hq : C / (D.R.k * D.host.v) ≤ C₂ / (D.R.k * D.host.v) :=
    div_le_div_of_nonneg_right h (mul_nonneg hk hv.le)
  have hq0 : 0 ≤ C / (D.R.k * D.host.v) := div_nonneg hC (mul_nonneg hk hv.le)
  have hpw := pow_le_pow_left₀ hq0 hq (D.R.rS * (D.R.k - 2 - D.R.rS))
  exact mul_le_mul_of_nonneg_right (mul_le_mul hP hpw (pow_nonneg hq0 _) (le_trans hP0 hP))
    (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt MeasureTheory Finset
open scoped ENNReal InnerProductSpace

def triangularNumber (j : ℕ) : ℕ := ∑ i ∈ range j, (i + 1)

def superfactorial (j : ℕ) : ℝ := ∏ i ∈ range j, (i.factorial : ℝ)

def CellWeightBound (D : D7) : Prop :=
  ∀ (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)),
    inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' →
    RelPt D z z' γ p →
    0 < ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS z) (Tz D.R.k D.R.rS z') p ∧
    Gf D.R.k D.R.rS z z' γ ^ D.R.k ≤ ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS z) (Tz D.R.k D.R.rS z') p *
      (max (Gf D.R.k D.R.rS z z' γ) (Gf D.R.k D.R.rS z z' γ)⁻¹ *
        ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (2 * (D.R.m + 4))).prod)

def blockEndsFrom : ℕ → List (ℂ × ℕ) → List ℕ
  | _, [] => []
  | a, (_, s) :: bs => (a + s) :: blockEndsFrom (a + s) bs

def MinorModuliChain (δ : ℕ → ℝ) : ℕ → List (ℂ × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => δ (a + s) = δ a * ‖t‖ ^ s ∧ MinorModuliChain δ (a + s) bs

def L2WithSizeDecay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch : ℝ) : Prop :=
  UnitaryVolumeMass.ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun τ w w' W S γ p νR =>
    ∀ q : ℕ, (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2 →
      normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
        lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹ *
          sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

def HilbertSchmidtBoundWithSizeDecay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch : ℝ) : Prop :=
  UnitaryVolumeMass.ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun τ w w' W S γ p νR =>
    ∀ q : ℕ, (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2 →
    normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) / Module.finrank ℂ W.Wp ≤
      lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹ *
        sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1)))

def AbsWithSizeDecay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch : ℝ) : Prop :=
  UnitaryVolumeMass.ForAmpH D large₂ C' Cl Cg cb Cu cT CT C0 A C1 fun _ _ _ W S γ p νR =>
    ∀ q : ℕ, (q : ℝ) ≤ Cpr * D.R.k * (D.R.m : ℝ) ^ 2 →
    DminN W.z W.z' γ D.R.rS ≠ 0 →
      ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
        (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
        (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹ *
        sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-((q : ℝ) / ((D.R.rS : ℝ) + 1)))

def AbsAllParameters (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Cn C : ℝ) : Prop :=
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        Hyp D large₂ w w' C' Cl Cg cb Cu cT CT C0 A → DminN W.z W.z' γ D.R.rS ≠ 0 →
          ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
            (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
            (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def DegreeRatioUnitShiftBound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI I) A' → A'.deg / A.deg ≤ (D.R.r : ℝ) ^ (hilbertNinetyConstant * (I.card : ℝ))

section Fam

variable {eps : ℝ} (Fm : FamP eps)

def FamilyAbsWithConvergence (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ Ca : ℝ, 0 ≤ Ca ∧ OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlusBranching.Conclusion4 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Ca ∧
      VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1

def FamilyDecayBound (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ Cd Ch : ℝ, 0 ≤ Ch ∧ ∀ Cpr : ℝ, ∀ C ≥ Cd, ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlusBranching.division_rows_rational_lattice (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def FamilyAbsFromMoments (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  VanishingOnXAndXPlusBranching.admF3 Fm Cg cb Cu cT CT C0 C1 → VanishingOnXAndXPlusBranching.adm6 → VanishingOnXAndXPlusBranching.adm7 → FamilyAbsWithConvergence Fm Cg cb Cu cT CT C0 A C1

def FamilyDecayFromAbs (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  VanishingOnXAndXPlusBranching.AdmFAt Fm Cg cb Cu cT CT C0 C1 → FamilyAbsWithConvergence Fm Cg cb Cu cT CT C0 A C1 → FamilyDecayBound Fm Cg cb Cu cT CT C0 A C1

def FamilyAbsWithDecay (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ Ca Ch : ℝ, 0 ≤ Ca ∧ 0 ≤ Ch ∧ ∀ Cpr : ℝ, OwnEv Fm fun C' Cl x i =>
    AbsWithSizeDecay (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch

def FamilyL2WithDecay (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ K Kh : ℝ, ∀ Cpr : ℝ, ∀ C ≥ K, ∀ Ch ≥ Kh, OwnEv Fm fun C' Cl x i =>
    HilbertSchmidtBoundWithSizeDecay (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch

def FamilyDegreeRatioUnitShiftBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ hilbertNinetyConstant : ℝ, 0 ≤ hilbertNinetyConstant ∧ ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
    DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant

def FamilyAbsAllParameters (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
    AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn Ca

def FamilyAbsAllAndConvergenceOfHypotheses (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  VanishingOnXAndXPlusBranching.AdmFAt Fm Cg cb Cu cT CT C0 C1 →
    FamilyAbsAllParameters Fm Cg cb Cu cT CT C0 A C1 ∧
      OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1

def FamilyAbsDecayAndConvergenceOfHypotheses (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  VanishingOnXAndXPlusBranching.AdmFAt Fm Cg cb Cu cT CT C0 C1 → FamilyAbsWithDecay Fm Cg cb Cu cT CT C0 A C1 ∧
    OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1

end Fam

end Formalism.MainNotions.BridgeLemma

end
