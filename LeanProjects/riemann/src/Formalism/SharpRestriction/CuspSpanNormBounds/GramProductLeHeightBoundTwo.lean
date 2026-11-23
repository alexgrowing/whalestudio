import Formalism.SharpRestriction.CuspSpanNormBounds.GramFlagFamilyOfPositive

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  unfold Scale.b Scale.L
  have h1 : 1 ≤ s.x ^ s.eps := Real.one_le_rpow (le_of_lt s.one_lt_alt) s.eps_pos.le
  have h2 := Real.add_one_le_exp (s.x ^ s.eps)
  linarith

theorem T_le_of_hyp {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C' Cl Cg cb Cu cT CT C0 A : ℝ}
    (hH : Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) (w : D.what₂.Word) :
    ((Tu D w : ℕ) : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := by
  obtain ⟨⟨hS0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, -, -⟩ := hS0
  exact (h23 w).2

section Bound

variable (D : D7) (u u' : D.what₂.Word)

def Pt (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))

theorem sizeZ_eq (b C : ℝ) (Z : GramM D) : Cnt.sizeZ D b C Z = ∏ τ, Pt D b C Z τ := rfl

theorem absDl_le_Pt {b C : ℝ} (hb : 0 < b) (Z : GramM D) (τ : D.what₂.Tau) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 (D.R.rS + 1)) :
    Cnt.absDl D Z l τ ≤ b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ := by
  have hH2 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb _
  calc Cnt.absDl D Z l τ
      = b ^ (C * (D.R.m : ℝ) ^ 2) * (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by field_simp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2) * max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hH2.le
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_prod_max hl (fun l => Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))) hH2.le

theorem gram_product_le_height_bound_two (Z : GramM D) {b C CT : ℝ} (hb : 2 ≤ b) (h1T : 1 ≤ ((Tu D u : ℕ) : ℝ))
    (hT : ((Tu D u : ℕ) : ℝ) ≤ b ^ (CT * (D.R.m : ℝ))) (hT' : ((Tu D u' : ℕ) : ℝ) ≤ b ^ (CT * (D.R.m : ℝ)))
    (hr : 1 ≤ D.R.rS) (hC : 3 + 2 * |CT| ≤ C) : localGramProduct D u u' Z ≤ Cnt.HHZ D b C Z := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hH2 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb0 _
  have hβ1 : 1 ≤ b ^ (CT * (D.R.m : ℝ)) := h1T.trans hT
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hP1 : ∀ τ, 1 ≤ Pt D b C Z τ := fun τ => one_le_prod_max _ _
  have hr1 : D.R.rS + 1 ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hr0 : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, by omega⟩

  have hG : ∀ τ, |Cnt.Gz D (Tu D u) (Tu D u') Z τ| ≤
      2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := by
    intro τ
    have ha0 := absDl_nonneg D Z (D.R.rS + 1) τ
    have hd0 := absDl_nonneg D Z D.R.rS τ
    have ha := absDl_le_Pt D (C := C) hb0 Z τ hr1
    have hd := absDl_le_Pt D (C := C) hb0 Z τ hr0
    have hX0 : 0 ≤ (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := sq_nonneg _
    have ha2 := pow_le_pow_left₀ ha0 ha 2
    have hd2 := pow_le_pow_left₀ hd0 hd 2
    have hc0 : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) := by positivity
    have hc : ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 := by
      rw [sq]; exact mul_le_mul hT hT' (Nat.cast_nonneg _) (by linarith)
    have hβ2 : 1 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 := one_le_pow₀ hβ1
    have hcd : ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) * Cnt.absDl D Z D.R.rS τ ^ 2 ≤
        (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
      mul_le_mul hc hd2 (sq_nonneg _) (by positivity)
    have hcd0 : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) * Cnt.absDl D Z D.R.rS τ ^ 2 := by positivity
    have hXβ : (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 ≤
        (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
      le_mul_of_one_le_left hX0 hβ2
    have hβX : 0 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 := by positivity
    unfold Cnt.Gz
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Cnt.absDl D Z (D.R.rS + 1) τ)]

  have hprod : |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| ≤
      (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * (Cnt.sizeZ D b C Z) ^ 2 := by
    rw [Finset.abs_prod]
    calc (∏ τ, |Cnt.Gz D (Tu D u) (Tu D u') Z τ|)
        ≤ ∏ τ, 2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2) * Pt D b C Z τ) ^ 2 :=
          Finset.prod_le_prod (fun τ _ => abs_nonneg _) (fun τ _ => hG τ)
      _ = _ := by
          rw [sizeZ_eq, ← D.what₂.card_Tau]
          simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
          ring

  have hexp : (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f ≤
      (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) := by
    have e1 : 2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 ≤
        b ^ (1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_one, Real.rpow_mul hb0.le (CT * (D.R.m : ℝ)) 2,
        Real.rpow_mul hb0.le (C * (D.R.m : ℝ) ^ 2) 2, Real.rpow_two, Real.rpow_two]
      have : 0 ≤ (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2 := by positivity
      nlinarith
    have hCT : CT ≤ |CT| := le_abs_self CT
    have hCT0 : 0 ≤ |CT| := abs_nonneg CT
    have k1 : 4 ≤ C * (D.R.m : ℝ) - 2 := by nlinarith
    have k2 : 1 + 2 * |CT| * (D.R.m : ℝ) ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
    have k3 : 1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2 ≤ C * (D.R.m : ℝ) ^ 2 * (C * (D.R.m : ℝ)) := by
      have hCm2 : 0 ≤ C * (D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc (2 * (b ^ (CT * (D.R.m : ℝ))) ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f
        ≤ (b ^ (1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2)) ^ D.R.f :=
          pow_le_pow_left₀ (by positivity) e1 _
      _ = b ^ ((1 + CT * (D.R.m : ℝ) * 2 + C * (D.R.m : ℝ) ^ 2 * 2) * D.R.f) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * (D.R.m : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1
          have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
          nlinarith
      _ = _ := Real.rpow_mul hb0.le _ _
  have hs1 := one_le_sizeZ D b C Z
  have h5 : (Cnt.sizeZ D b C Z) ^ 2 ≤ (Cnt.sizeZ D b C Z) ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hg0 : 0 ≤ ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) := by positivity
  have hg : ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (Nat.cast_nonneg _)) (Nat.cast_inv_le_one (gS D))
  unfold localGramProduct Cnt.HHZ
  calc (∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)
      ≤ |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hg0
    _ ≤ |∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ| := mul_le_of_le_one_right (abs_nonneg _) hg
    _ ≤ _ := hprod
    _ ≤ (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) * (Cnt.sizeZ D b C Z) ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)

end Bound

section Fam

def LatticeIdentityGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F')

theorem gram_flag_of_identity (hI : LatticeIdentityGeneric) (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)
    {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hC : 3 + 2 * |CT| ≤ C) :
    GenericTermDetProductBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro hH F0 he hz0 Λ hΛr Z _ F' hT' hgen hZE
  have hid := hI D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen
  have hone := one_le_generic_gram_value D large₂ u u' hH F0 he hz0 Λ hΛr F' hT' hgen
  have hZ : localGramProduct D u u' Z = localGramProduct D u u' (ZhatL (lf D F0) F') := gram_product_equiv_invariant D u u' hZE
  have hSt : Cnt.Stand D u u' := hH.2.1
  have h3 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hSt.2.2.2.1
  refine ⟨hid.trans hZ.symm, ?_, gram_product_le_height_bound_two D u u' Z (two_le_b large₂.sc) (by linarith) (T_le_of_hyp hH u)
    (T_le_of_hyp hH u') hSt.1 hC⟩
  rw [hZ, ← hid]
  exact hone

theorem gram_flag_family_of_identity (hI : LatticeIdentityGeneric) {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ) :
    FamilyGenericTermDetProductBound Fm Cg cb Cu cT CT C0 A :=
  ⟨3 + 2 * |CT|, fun _ hC => ⟨0, fun x _ i u u' => gram_flag_of_identity hI (Fm.D x i) (Fm.L x i) u u' hC⟩⟩

end Fam

end Formalism.MainNotions.GramProductBounds

end
