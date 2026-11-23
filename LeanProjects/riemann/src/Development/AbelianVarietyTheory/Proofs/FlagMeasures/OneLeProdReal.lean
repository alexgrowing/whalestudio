import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPartnerLift
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxNOneMulAbsNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTermsGramClassOverSublatticeStatement

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.Partner

section Count

open Formalism.MainNotions.S.Cnt GlobalTheory.Mass
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cntCl_mono {α : Type} {X Y : Set α} (h : X ⊆ Y) (R : α → α → Prop) : cntCl X R ≤ cntCl Y R := by
  unfold cntCl
  have hsub : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} ⊆
      (fun O => O ∩ X) '' {O : Set α | ∃ a ∈ Y, O = {b | b ∈ Y ∧ R a b}} := by
    rintro O ⟨a, ha, rfl⟩
    refine ⟨{b | b ∈ Y ∧ R a b}, ⟨a, h ha, rfl⟩, ?_⟩
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_, hc⟩, hcX⟩
      exact ⟨hcX, hc⟩
    · rintro ⟨hcX, hc⟩
      exact ⟨⟨h hcX, hc⟩, hcX⟩
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

variable {D : D7}

theorem one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  exact one_le_prod_real fun τ _ => one_le_prod_real fun l _ => le_max_left _ _

theorem prod_Gz_le {b C B T T' : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C) (hr : 1 ≤ D.R.rS) (hT : 1 ≤ T * T') (hB : T * T' ≤ B)
    (Z : GramM D) :
    ∏ τ, Gz D T T' Z τ ≤ (B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2 := by
  obtain ⟨hcard, -, -, -, hrd, -⟩ := GlobalTheory.real_places_facts D
  have hH : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos (by linarith) _
  have hB1 : 1 ≤ B := hT.trans hB
  have hnn : ∀ l τ, 0 ≤ absDl D Z l τ := fun l τ => by
    unfold absDl absReal
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hM1 : ∀ l τ, 1 ≤ max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := fun l τ => le_max_left _ _
  have hsq : ∀ l τ, absDl D Z l τ ^ 2 ≤
      (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := fun l τ => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (hnn l τ) ?_ 2
    have h := le_max_right 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))
    rw [div_le_iff₀ hH] at h
    linarith
  have hpt : ∀ τ, |Gz D T T' Z τ| ≤ B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 *
      (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
        max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ^ 2 := fun τ => by
    unfold Gz
    have ha := hsq (D.R.rS + 1) τ
    have hc := hsq D.R.rS τ
    have hMa := one_le_pow₀ (n := 2) (hM1 (D.R.rS + 1) τ)
    have hMc := one_le_pow₀ (n := 2) (hM1 D.R.rS τ)
    have hK := sq_nonneg (b ^ (C * (D.R.m : ℝ) ^ 2))
    have hA0 := sq_nonneg (absDl D Z (D.R.rS + 1) τ)
    have hC0 := sq_nonneg (absDl D Z D.R.rS τ)
    have e1 := mul_nonneg (sub_nonneg.2 hB1) (mul_nonneg (mul_nonneg hK (zero_le_one.trans hMa)) (zero_le_one.trans hMc))
    have e2 := mul_nonneg (mul_nonneg hK (zero_le_one.trans hMa)) (sub_nonneg.2 hMc)
    have e3 := mul_nonneg (zero_le_one.trans hT) hC0
    have e4 := mul_nonneg (sub_nonneg.2 hB) hC0
    have e5 := mul_nonneg (zero_le_one.trans hB1) (sub_nonneg.2 hc)
    have e6 := mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hB1) hK) (zero_le_one.trans hMc)) (sub_nonneg.2 hMa)
    rw [abs_le]
    constructor <;> nlinarith [e1, e2, e3, e4, e5, e6, ha, hA0]
  have hprod : ∏ τ, Gz D T T' Z τ ≤ ∏ τ, (B * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 *
      (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
        max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ^ 2) :=
    calc ∏ τ, Gz D T T' Z τ ≤ |∏ τ, Gz D T T' Z τ| := le_abs_self _
      _ = ∏ τ, |Gz D T T' Z τ| := Finset.abs_prod _ _
      _ ≤ _ := Finset.prod_le_prod (fun τ _ => abs_nonneg _) (fun τ _ => hpt τ)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Finset.prod_pow] at hprod
  have hsz : ∏ τ, (max 1 (absDl D Z (D.R.rS + 1) τ / b ^ (C * (D.R.m : ℝ) ^ 2)) *
      max 1 (absDl D Z D.R.rS τ / b ^ (C * (D.R.m : ℝ) ^ 2))) ≤ sizeZ D b C Z := by
    unfold sizeZ
    refine Finset.prod_le_prod (fun τ _ => mul_nonneg (zero_le_one.trans (hM1 _ _)) (zero_le_one.trans (hM1 _ _))) ?_
    intro τ _
    have hmem1 : D.R.rS + 1 ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have hmem2 : D.R.rS ∈ (Finset.Icc 1 (D.R.rS + 1)).erase (D.R.rS + 1) :=
      Finset.mem_erase.2 ⟨by omega, Finset.mem_Icc.2 ⟨hr, by omega⟩⟩
    rw [← Finset.mul_prod_erase _ _ hmem1, ← Finset.mul_prod_erase _ _ hmem2]
    have h1 : 1 ≤ ∏ l ∈ ((Finset.Icc 1 (D.R.rS + 1)).erase (D.R.rS + 1)).erase D.R.rS,
        max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := one_le_prod_real fun l _ => hM1 l τ
    have ha := hM1 (D.R.rS + 1) τ
    have hc := hM1 D.R.rS τ
    rw [← mul_assoc]
    exact le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans ha) (zero_le_one.trans hc)) h1
  refine hprod.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hsz 2) (pow_nonneg ?_ _))
  · exact Finset.prod_nonneg fun τ _ => mul_nonneg (zero_le_one.trans (hM1 _ _)) (zero_le_one.trans (hM1 _ _))
  · exact mul_nonneg (by linarith) (sq_nonneg _)

theorem sizes {b C CT : ℝ} (hb : 1 ≤ b) (hC : 2 ≤ C) (hCT : CT ≤ C) (hr : 1 ≤ D.R.rS) {T T' : ℝ} (h1 : 1 ≤ T)
    (h1' : 1 ≤ T') (hT : T ≤ b ^ (CT * D.R.m)) (hT' : T' ≤ b ^ (CT * D.R.m)) (Z : GramM D) :
    1 ≤ HHZ D b C Z ∧ T ^ D.R.f ≤ HHZ D b C Z ∧ ∏ τ, Gz D T T' Z τ ≤ HHZ D b C Z := by
  have hb0 : 0 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hs := one_le_sizeZ b C Z
  have hs4 : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hs
  have hE : HHZ D b C Z = b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
    unfold HHZ
    rw [← Real.rpow_mul hb0]
  have hE0 : 0 ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by positivity
  have hbE : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.one_le_rpow hb hE0
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]
    exact one_le_mul_of_one_le_of_one_le hbE hs4
  · rw [hE]
    have e1 : T ^ D.R.f ≤ (b ^ (CT * D.R.m)) ^ D.R.f := pow_le_pow_left₀ (by linarith) hT _
    rw [← Real.rpow_mul_natCast hb0] at e1
    have hx : CT * D.R.m * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
      have q1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hCT) (by linarith : (0 : ℝ) ≤ D.R.m)) hf
      have q2 : (1 : ℝ) ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
      have q3 := mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m)) hf)
        (sub_nonneg.2 q2)
      nlinarith
    have e2 := Real.rpow_le_rpow_of_exponent_le hb hx
    calc T ^ D.R.f ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := e1.trans e2
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hs4
  · have hTT : 1 ≤ T * T' := one_le_mul_of_one_le_of_one_le h1 h1'
    have hB : T * T' ≤ b ^ (CT * D.R.m) * b ^ (CT * D.R.m) :=
      mul_le_mul hT hT' (by linarith) (Real.rpow_nonneg hb0 _)
    have hP := prod_Gz_le (C := C) hb (by linarith) hr hTT hB Z
    have eB : (b ^ (CT * D.R.m) * b ^ (CT * D.R.m) * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f =
        b ^ ((2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2) * D.R.f) := by
      rw [← Real.rpow_add hbp, ← Real.rpow_mul_natCast hb0 _ 2, ← Real.rpow_add hbp,
        ← Real.rpow_mul_natCast hb0]
      congr 1
      push_cast
      ring
    rw [eB] at hP
    have hx : (2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
      have q1 : 2 * CT * D.R.m + 2 * C * (D.R.m : ℝ) ^ 2 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) := by
        have r1 := mul_nonneg (sub_nonneg.2 hCT) (by linarith : (0 : ℝ) ≤ D.R.m)
        have r2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (by linarith : (0 : ℝ) ≤ D.R.m))
          (by linarith : (0 : ℝ) ≤ D.R.m - 1)
        have r3 : (4 : ℝ) ≤ C * D.R.m := by nlinarith
        have r4 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C) (sq_nonneg (D.R.m : ℝ))) (sub_nonneg.2 r3)
        nlinarith
      have := mul_le_mul_of_nonneg_right q1 hf
      linarith
    have e2 := Real.rpow_le_rpow_of_exponent_le hb hx
    have hs2 : sizeZ D b C Z ^ 2 ≤ sizeZ D b C Z ^ 4 := pow_le_pow_right₀ hs (by norm_num)
    rw [hE]
    exact hP.trans (mul_le_mul e2 hs2 (sq_nonneg _) (by linarith))

theorem final_arith {N De H C : ℝ} {r f : ℕ} (hr : 1 ≤ r) (hN0 : 0 ≤ N) (hN : N ≤ H) (hD0 : 1 ≤ De) (hD : De ≤ H)
    (hC : 37 ≤ C) :
    N ^ (2 * r) * De ^ r * 9 ^ (1 * f) * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2) ≤ C ^ f * H ^ (C * (r : ℝ) ^ 2) := by
  have hH : 1 ≤ H := hD0.trans hD
  have h1 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0 hN _
  have h2 : De ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hD _
  have h3 : (9 : ℝ) ^ (1 * f) ≤ C ^ f := by
    rw [one_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hexp : ((2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2) : ℕ) : ℝ) ≤ C * (r : ℝ) ^ 2 := by
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    nlinarith
  have h4 : H ^ (2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2)) ≤ H ^ (C * (r : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hH hexp
  calc N ^ (2 * r) * De ^ r * 9 ^ (1 * f) * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2)
      ≤ H ^ (2 * r) * H ^ r * C ^ f * H ^ (9 * 1 + 9 * 1 * r + 16 * r ^ 2) := by
        have hH0 : 0 ≤ H := by linarith
        have s1 : N ^ (2 * r) * De ^ r ≤ H ^ (2 * r) * H ^ r :=
          mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (pow_nonneg hH0 _)
        have s2 : N ^ (2 * r) * De ^ r * 9 ^ (1 * f) ≤ H ^ (2 * r) * H ^ r * C ^ f :=
          mul_le_mul s1 h3 (by positivity) (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
        exact mul_le_mul_of_nonneg_right s2 (pow_nonneg hH0 _)
    _ = C ^ f * H ^ (2 * r + r + (9 * 1 + 9 * 1 * r + 16 * r ^ 2)) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ C ^ f * H ^ (C * (r : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h4 (pow_nonneg (by linarith) _)

theorem partners_le : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.count_terms_gramClass_over_sublattice Cg cb Cu cT CT C0 A
  refine ⟨max (max C₀ 37) CT, ?_⟩
  intro D large₂ u u' C' Cl hCl hHyp F0 he hz Λ hΛ F' hterm hgen hrel Z hZ
  have hCC₀ : C₀ ≤ max (max C₀ 37) CT := (le_max_left _ _).trans (le_max_left _ _)
  have hC37 : (37 : ℝ) ≤ max (max C₀ 37) CT := (le_max_right _ _).trans (le_max_left _ _)
  have hCT : CT ≤ max (max C₀ 37) CT := le_max_right _ _
  have hHyp' := hHyp
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hHyp'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTr, -, -⟩ := hS0
  obtain ⟨hr, -, -, hT3, hT3', -, -, hg0, hg1, -, -, -, -⟩ := hSt
  have hb : 1 ≤ large₂.sc.b := by
    show 1 ≤ Real.exp (large₂.sc.x ^ large₂.sc.eps)
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hTu : ((Tu D u : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (hTr u).2
  have hTu' : ((Tu D u' : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (hTr u').2
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℕ) := by exact_mod_cast (by omega : 1 ≤ Tu D u)
  have hT1' : (1 : ℝ) ≤ (Tu D u' : ℕ) := by exact_mod_cast (by omega : 1 ≤ Tu D u')
  have hTne : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTne' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hg0.ne_zero hg1.ne_zero
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hΛ' := hΛ
  obtain ⟨-, ⟨hlat, huni, hlift, -⟩, hXS⟩ := hΛ'
  have hterm' := hterm
  obtain ⟨⟨hlift', -, hG'⟩, -, hXS'⟩ := hterm'
  have hfr : ∀ b, frame (lf D F0) b ∈ Λ := frame_mem_of_XS (lf D F0) hlift hXS
  have hfr' : ∀ b, frame F' b ∈ Λ := frame_mem_of_XS F' hlift' hXS'
  have hUUE : UUE Λ (lf D F0) F' = Xplus (lf D F0) ⊔ Xplus F' := UUE_eq (lf D F0) F' hlift hlift' hfr hfr'
  have hW : WHyp D (lf D F0) (Wsp D) := Formalism.MainNotions.WHyp_Wsp D u (by omega) (lf D F0) he hz
  have hRP := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  have hPD := hRP.1.1
  have hInt := (hRP.2 Λ hΛ).1
  have hsz := sizes (D := D) hb (by linarith) hCT hr hT1 hT1' hTu hTu' (ZhatL (lf D F0) F')
  have hszZ := sizes (D := D) hb (by linarith) hCT hr hT1 hT1' hTu hTu' Z
  have hHle : Hp Λ (lf D F0) F' ≤ orth (hS D) (Xplus (lf D F0)) := by
    intro x hx
    unfold Hp at hx
    rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
    intro y hy
    apply hx y
    show y ∈ UUE Λ (lf D F0) F'
    rw [hUUE]
    exact Submodule.mem_sup_left hy
  have hbot : (Xplus (lf D F0) ⊔ Xplus F') ⊓ orth (hS D) (Xplus (lf D F0) ⊔ Xplus F') = ⊥ :=
    sup_inf_orth (lf D F0).fl F'.fl hG'
  have hHX : Hp Λ (lf D F0) F' ⊓ Xsp (lf D F0) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx3 : x ∈ (Xplus (lf D F0) ⊔ Xplus F') ⊓ orth (hS D) (Xplus (lf D F0) ⊔ Xplus F') := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_sup_left ?_, ?_⟩
      · exact (le_sup_left : (lf D F0).fl.X ≤ (lf D F0).fl.X ⊔ Submodule.span D.host.E {(lf D F0).fl.z}) hx2
      · rw [← hUUE]
        exact hx1
    rw [hbot] at hx3
    exact hx3
  have hfinV := Formalism.MainNotions.finrank_hS D
  have horth := finrank_orth_le (lf D F0).fl F'.fl hG' hTne hTne'
  have hHpfin : finrank D.host.E (Hp Λ (lf D F0) F') + 2 * (D.R.rS + 1) ≤ finrank D.host.E (hS D).V := by
    unfold Hp
    rw [hUUE]
    exact horth
  have hThle : ∀ (F'' : Fg D ((Tu D u' : ℕ) : D.host.E)) (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
      Th Λ (lf D F0) F' F'' β ≤ Hp Λ (lf D F0) F' := by
    intro F'' β x hx
    unfold Th at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
    unfold ThPairs at hp
    exact (Submodule.mem_prod.1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hp).1).1).1
  have hThEq : ∀ (F'' : Fg D ((Tu D u' : ℕ) : D.host.E)) (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
      s0 Λ (lf D F0) F' F'' β D.R.k = 1 → Th Λ (lf D F0) F' F'' β = Hp Λ (lf D F0) F' := by
    intro F'' β hs
    unfold s0 at hs
    refine Submodule.eq_of_le_of_finrank_le (hThle F'' β) ?_
    omega
  by_cases hne : (Partners D Λ (lf D F0) F' Z).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : cntPartners D Λ (lf D F0) F' Z = 0 := by
      unfold cntPartners cntCl
      rw [hne]
      simp
    rw [h0]
    simp
  obtain ⟨F₁, -, -, -, β₁, -, hs₁⟩ := hne
  have hrank : finrank D.host.E (Hp Λ (lf D F0) F') = D.R.k - 1 := by
    have hE := hThEq F₁ β₁ hs₁
    unfold s0 at hs₁
    rw [hE] at hs₁
    omega
  have hsub : Partners D Λ (lf D F0) F' Z ⊆
      FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z (seen D (lf D F0) (Thp Λ (lf D F0) F')) := by
    rintro F'' ⟨hterm'', hgen'', hZ'', β, hpair, hs⟩
    refine ⟨hterm'', hZ'', ?_⟩
    have hterm3 := hterm''
    obtain ⟨⟨hlift'', -, hG''⟩, -, hXS''⟩ := hterm3
    have hfr'' : ∀ b, frame F'' b ∈ Λ := frame_mem_of_XS F'' hlift'' hXS''
    have hTh := hThEq F'' β hs
    intro w hw
    rw [mem_seen] at hw ⊢
    obtain ⟨x, hx, hxw⟩ := hw
    have hxΛ : x ∈ Λ := (Submodule.mem_inf.1 hx).1
    have hxH : x ∈ Hp Λ (lf D F0) F' := (Submodule.mem_inf.1 hx).2
    have hxT : x ∈ Th Λ (lf D F0) F' F'' β := by rw [hTh]; exact hxH
    obtain ⟨y, hy, hxy⟩ := exists_partner_lift hg (lf D F0) F' F'' β hlift hlift' hlift'' hfr hfr' hfr''
      hG'' hgen'' hpair hxΛ hxT
    refine ⟨y, hy, ?_⟩
    have := Submodule.add_mem _ hxw hxy
    rwa [sub_add_sub_cancel] at this
  have hPL0 : seen D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) :=
    seen_le_L0X (lf D F0) (Hp Λ (lf D F0) F') hHle
  have hrk : rkW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 := by
    rw [← hrank]
    exact rk_seen (lf D F0) hlat hW (Hp Λ (lf D F0) F') hHle hHX
  have hXle : Xplus (lf D F0) ≤ spanE (hS D) (UU Λ (lf D F0) F') := by
    show Xplus (lf D F0) ≤ UUE Λ (lf D F0) F'
    rw [hUUE]
    exact le_sup_left
  have hnd : spanE (hS D) (UU Λ (lf D F0) F') ⊓ orth (hS D) (spanE (hS D) (UU Λ (lf D F0) F')) = ⊥ := by
    show UUE Λ (lf D F0) F' ⊓ orth (hS D) (UUE Λ (lf D F0) F') = ⊥
    rw [hUUE]
    exact hbot
  have hdet : detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ NG Λ (lf D F0) F' :=
    det_seen_le (lf D F0) hlat huni hW (fun τ x hx => hPD τ x hx) hInt (UU Λ (lf D F0) F')
      (UU_le (lf D F0) F' hlift hlift') hXle hnd
  have hNG := GlobalTheory.LoopC.FrameDet.main D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hHyp F0 he hz Λ hΛ F' hterm hgen
  have hdetH : detW D (seen D (lf D F0) (Thp Λ (lf D F0) F')) ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') := by
    rw [hNG] at hdet
    exact hdet.trans hsz.2.2
  have hHh1 : 1 ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    one_le_mul_of_one_le_of_one_le hsz.1 hszZ.1
  have hHZ : HHZ D large₂.sc.b (max (max C₀ 37) CT) Z ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    le_mul_of_one_le_left (by linarith [hszZ.1]) hsz.1
  have hZ'le : HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    le_mul_of_one_le_right (by linarith [hsz.1]) hszZ.1
  have hDeH : max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))) ≤
      HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    max_le hHh1 (hdetH.trans hZ'le)
  have hDe3 : max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))) ≤
      (HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z) ^ 3 :=
    hDeH.trans (le_self_pow₀ hHh1 (by norm_num))
  have hcnt := hC₀ (max (max C₀ 37) CT) hCC₀ D large₂ u u' C' Cl hCl hHyp F0 he hz Λ hΛ Z hZ 1 le_rfl hk1
    (seen D (lf D F0) (Thp Λ (lf D F0) F')) hPL0 hrk
    (max 1 (detW D (seen D (lf D F0) (Thp Λ (lf D F0) F'))))
    (HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z)
    (le_max_left _ _) (le_max_right _ _) hHZ hDe3
  have hN0 : 0 ≤ NT D u := by unfold NT; positivity
  have hN : NT D u ≤ HHZ D large₂.sc.b (max (max C₀ 37) CT) (ZhatL (lf D F0) F') * HHZ D large₂.sc.b (max (max C₀ 37) CT) Z :=
    (hsz.2.1 : NT D u ≤ _).trans hZ'le
  have hfin := final_arith (f := D.R.f) hr hN0 hN (le_max_left _ _) hDeH hC37
  calc (cntPartners D Λ (lf D F0) F' Z : ℝ≥0∞)
      ≤ (cntCl (FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z (seen D (lf D F0) (Thp Λ (lf D F0) F')))
          (TEqv D Λ (lf D F0)) : ℝ≥0∞) := by
        unfold cntPartners
        exact_mod_cast cntCl_mono hsub _
    _ ≤ _ := hcnt
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

end Count

end GlobalTheory.LoopC.Partner
