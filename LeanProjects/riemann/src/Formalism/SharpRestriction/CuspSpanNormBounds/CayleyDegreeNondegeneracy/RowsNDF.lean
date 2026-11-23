import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_q_bound {m k r c cf a2 : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hcf : cf ≤ m)
    (ha2 : a2 ≤ k) :
    (r + 1) * (4 * (c * k) + 4 * (c * (k + m) * m + c * cf) + 4 * (c * r ^ 2) + a2 / 2 + 12 * (r + 1) ^ 2) + 1 ≤
      (9 * c + 3) * k * m ^ 2 := by
  subst hm
  have hs0 : 0 ≤ r + 1 := by linarith
  have hs1 : 1 ≤ r + 1 := by linarith
  have hk2 : 2 * (r + 1) ≤ k := by linarith
  have hk5 : 5 ≤ k := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hck : 0 ≤ c * k := mul_nonneg hc hk0
  have P1 : c * cf * (r + 1) ≤ c * (2 * r + 2) * (r + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcf hc) hs0
  have P2 : a2 * (r + 1) ≤ k * (r + 1) := mul_le_mul_of_nonneg_right ha2 hs0
  have P3 : c * r ^ 2 * (r + 1) ≤ c * (r + 1) ^ 2 * (r + 1) := by
    have : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) hs0
  have hss : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
  have Q1 : c * k * (r + 1) ≤ c * k * (r + 1) ^ 2 := mul_le_mul_of_nonneg_left hss hck
  have Q2 : c * (r + 1) ^ 2 * (2 * (r + 1)) ≤ c * (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  have Q3 : c * (r + 1) ^ 2 * 5 ≤ c * (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk5 (by positivity)
  have Q4 : k * (r + 1) ≤ k * (r + 1) ^ 2 := mul_le_mul_of_nonneg_left hss hk0
  have Q5 : (r + 1) ^ 2 * (2 * (r + 1)) ≤ (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  have Q6 : (r + 1) ^ 2 * 5 ≤ (r + 1) ^ 2 * k := mul_le_mul_of_nonneg_left hk5 (by positivity)
  have Q7 : 1 ≤ (r + 1) ^ 2 := by nlinarith
  nlinarith [P1, P2, P3, Q1, Q2, Q3, Q4, Q5, Q6, Q7, mul_nonneg hc hs0]

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_one_le_HHZ' (D : D7) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b c Z := by
  have hb : 1 ≤ large₂.sc.b := by
    have h := exp_one_le_b_rpow large₂ (le_refl (1 : ℝ))
    rw [Real.rpow_one] at h
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsz : 1 ≤ Cnt.sizeZ D large₂.sc.b c Z := by
    have key : ∀ {ι : Type} (s : Finset ι) (g : ι → ℝ), (∀ i ∈ s, 1 ≤ g i) → 1 ≤ ∏ i ∈ s, g i :=
      fun s g h => by simpa using Finset.prod_le_prod (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) h
    unfold Cnt.sizeZ
    exact key _ _ (fun τ _ => key _ _ (fun l _ => le_max_left _ _))
  unfold Cnt.HHZ
  rw [← Real.rpow_mul (by linarith)]
  refine one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hb ?_) (one_le_pow₀ hsz)
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have : c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) = c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f := by ring
  rw [this]
  positivity

theorem rows_HHZ_mono (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c') (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ≤ HHZ D large₂.sc.b c Z := by
  have hb : 1 ≤ large₂.sc.b := by
    have h := exp_one_le_b_rpow large₂ (le_refl (1 : ℝ))
    rw [Real.rpow_one] at h
    linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (rows_HHZ_cmp hrd hb c' c Z).trans ?_
  unfold Cnt.HHZ
  rw [← Real.rpow_mul (by linarith)]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb ?_) (by positivity)
  rw [max_eq_left (by linarith)]
  have hm : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by
    exact_mod_cast Formalism.MainNotions.BridgeLemma.d_m_eq (D := D)
  rw [hm]
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have key : 0 ≤ (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c - c') * (2 * (D.R.rS : ℝ) + 2) * (c + c' - 2) := by
    have a1 : 0 ≤ c - c' := by linarith
    have a2 : 0 ≤ c + c' - 2 := by linarith
    positivity
  have e : c * (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c * (2 * (D.R.rS : ℝ) + 2)) -
      (c' ^ 2 * (2 * (D.R.rS : ℝ) + 2) ^ 3 * D.R.f +
        4 * ((c - c') * (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))) =
      (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c - c') * (2 * (D.R.rS : ℝ) + 2) * (c + c' - 2) := by ring
  linarith

theorem rows_stHH_mono {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c')
    (h : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hT hR
  obtain ⟨a1, a2, a3, Z, hZ, hm⟩ := h hH F0 he hz Λ hΛ F' hT hR
  have mono := rows_HHZ_mono large₂ (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) h1 h2 (ZhatL (lf D F0) F')
  exact ⟨a1.trans mono, a2.trans mono, a3.trans mono, Z, hZ,
    fun j I J hd => ⟨(hm j I J hd).1.trans mono, (hm j I J hd).2.trans mono⟩⟩

theorem rows_stVol_mono {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c')
    (h : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A c') :
    VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A c := by
  unfold VanishingOnXAndXPlus.TermVolumeSmallCellBound UnitaryVolumeMass.stVol at h ⊢
  intro hH t ht hr
  refine (h hH t ht hr).trans ?_
  have mono := rows_HHZ_mono large₂ (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) h1 h2 (ZhatL (X.fl t) (X.fl' t))
  have o1 := rows_one_le_HHZ' D large₂ c' (ZhatL (X.fl t) (X.fl' t))
  have o2 := rows_one_le_HHZ' D large₂ c (ZhatL (X.fl t) (X.fl' t))
  have hr2 : (0 : ℝ) ≤ (D.R.rS : ℝ) ^ 2 := by positivity
  rcases le_total 0 c' with hc' | hc'
  · calc _ ≤ HHZ D large₂.sc.b c (ZhatL (X.fl t) (X.fl' t)) ^ (c' * (D.R.rS : ℝ) ^ 2) :=
          Real.rpow_le_rpow (by linarith) mono (mul_nonneg hc' hr2)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le o2 (mul_le_mul_of_nonneg_right h1 hr2)
  · calc _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos o1 (mul_nonpos_of_nonpos_of_nonneg hc' hr2)
      _ ≤ _ := Real.one_le_rpow o2 (mul_nonneg (by linarith) hr2)

include Y in

theorem rows_dim_pos {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hF : UnitaryVolumeMass.FormAt D u) :
    0 < dimPi (hc := D.hcW) u := by
  obtain ⟨-, hD, hC0⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, hdu, -⟩ := hD
  have hlow := (hdu u).1
  have hG : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) := zpow_pos (lt_trans zero_lt_one (D.mem u).A.one_lt_gammaP) _
  have hpos : 0 < (D.duS u : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hG (d_Dstar_pos (D := D))) (by linarith)) hlow
  have hform := hF Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows
  have hnn : 0 ≤ dimPi (hc := D.hcW) u := by
    unfold dimPi
    exact Finset.prod_nonneg fun τ _ => Nat.cast_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at hform
    rw [← hform] at hpos
    exact absurd hpos (lt_irrefl 0)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def rows_NDF : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C

def rows_DegF : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsDeg (X x hx i) (Y x hx i u u') C

def rows_OneF : Prop :=
  ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsOne (X x hx i) (Y x hx i u u') C

theorem rows_RowsF_of (h1 : rows_NDF Fm C1 X Y) (h2 : rows_DegF Fm C1 X Y) (h3 : rows_OneF Fm C1 X Y) :
    RowsF Fm C1 X Y := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨E1, hE1⟩ := h1 Cg cb Cu cT CT C0 A
  obtain ⟨E2, hE2⟩ := h2 Cg cb Cu cT CT C0 A
  obtain ⟨E3, hE3⟩ := h3 Cg cb Cu cT CT C0 A
  refine ⟨max E1 (max E2 E3), fun C hC => ?_⟩
  have hA := ((hE1 C (le_of_max_le_left hC)).and (hE2 C (le_of_max_le_left (le_of_max_le_right hC)))).and
    (hE3 C (le_of_max_le_right (le_of_max_le_right hC)))
  exact hA.mono fun C' Cl x i h hx u u' hH => ⟨h.1.1 hx u u' hH, h.1.2 hx u u' hH, h.2 hx u u' hH⟩

def rows_TiesF : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    TermPtsTie (X x hx i) (Y x hx i u u') ∧ @LatticeDeterminantFactorization (Fm.D x i) (X x hx i) u u' ∧ wordPairEntriesInLattice (X x hx i) u u'

def rows_AmpF : Prop :=
  ∀ Cg cb Cu cT CT C0 A Cpr : ℝ, ∃ C C2 Ch : ℝ, 0 ≤ Ch ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ

theorem rows_NDF_of (hAdm : VanishingOnXAndXPlus.AdmF Fm C1 X Y) (hAmp : rows_AmpF Fm C1) (hT : rows_TiesF Fm C1 X Y) :
    rows_NDF Fm C1 X Y := by
  unfold rows_NDF
  intro Cg cb Cu cT CT C0 A
  obtain ⟨-, -, -, -, -, -, -, h10a, -, -, -, h14, -, -, -, -, hrest⟩ := hAdm
  obtain ⟨-, -, -, -, -, -, -, -, h6, -, h8, -, h10b, -, -, h20, -, -, h27, hVol⟩ := hrest Cg cb Cu cT CT C0 A
  obtain ⟨C27, h27⟩ := h27
  obtain ⟨CV, hVol⟩ := hVol
  obtain ⟨C20, h20⟩ := h20 3
  obtain ⟨c, hc27, hcV, hc20, hc2, hc27', hcV'⟩ : ∃ c : ℝ, C27 ≤ c ∧ CV ≤ c ∧ C20 ≤ c ∧ 2 ≤ c ∧
      2 - C27 ≤ c ∧ 2 - CV ≤ c := by
    refine ⟨|C27| + |CV| + |C20| + 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith [abs_nonneg C27, abs_nonneg CV, abs_nonneg C20, le_abs_self C27, le_abs_self CV,
        le_abs_self C20, neg_abs_le C27, neg_abs_le CV]
  obtain ⟨Ca, C2, Ch, hCh, hAm⟩ := hAmp Cg cb Cu cT CT C0 A (9 * c + 3)
  refine ⟨max c (max 1 (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))), fun C hC => ?_⟩
  have hcC : c ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCV : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  obtain ⟨x1a, h20x⟩ := h20 c hc20
  obtain ⟨x2, h27x⟩ := h27
  obtain ⟨x3, hVx⟩ := hVol
  obtain ⟨x4, hAmx⟩ := hAm 1 one_pos
  obtain ⟨x5, h6x⟩ := h6 1 one_pos
  obtain ⟨x6, h8x⟩ := h8
  obtain ⟨x7, h10bx⟩ := h10b
  obtain ⟨x8, -, hkx⟩ := ev_kLow (Fm := Fm) (max C2 0)
  obtain ⟨x9, -, hLx⟩ := ev_L (Fm := Fm) 1
  unfold OwnEv
  refine ⟨|x1a| + |x2| + |x3| + |x4| + |x5| + |x6| + |x7| + |x8| + |x9|, fun x hx0 i hx u u' hH => ?_⟩
  have ax := fun (a : ℝ) => le_abs_self a
  have bx := fun (a : ℝ) => abs_nonneg a
  have e1 : x1a ≤ x := by linarith [ax x1a, bx x2, bx x3, bx x4, bx x5, bx x6, bx x7, bx x8, bx x9]
  have e2 : x2 ≤ x := by linarith [ax x2, bx x1a, bx x3, bx x4, bx x5, bx x6, bx x7, bx x8, bx x9]
  have e3 : x3 ≤ x := by linarith [ax x3, bx x2, bx x1a, bx x4, bx x5, bx x6, bx x7, bx x8, bx x9]
  have e4 : x4 ≤ x := by linarith [ax x4, bx x2, bx x3, bx x1a, bx x5, bx x6, bx x7, bx x8, bx x9]
  have e5 : x5 ≤ x := by linarith [ax x5, bx x2, bx x3, bx x4, bx x1a, bx x6, bx x7, bx x8, bx x9]
  have e6 : x6 ≤ x := by linarith [ax x6, bx x2, bx x3, bx x4, bx x5, bx x1a, bx x7, bx x8, bx x9]
  have e7 : x7 ≤ x := by linarith [ax x7, bx x2, bx x3, bx x4, bx x5, bx x6, bx x1a, bx x8, bx x9]
  have e8 : x8 ≤ x := by linarith [ax x8, bx x2, bx x3, bx x4, bx x5, bx x6, bx x7, bx x1a, bx x9]
  have e9 : x9 ≤ x := by linarith [ax x9, bx x2, bx x3, bx x4, bx x5, bx x6, bx x7, bx x8, bx x1a]
  have hH' := hH
  obtain ⟨hH0, hSt, -⟩ := hH'
  have hH0' := hH0
  obtain ⟨hS0, -, -⟩ := hH0'
  obtain ⟨-, -, hm4, -, hlogf, -⟩ := hS0
  have hr1 : (1 : ℝ) ≤ ((Fm.D x i).R.rS : ℝ) := by exact_mod_cast hSt.1
  have hmr : ((Fm.D x i).R.m : ℝ) = 2 * ((Fm.D x i).R.rS : ℝ) + 2 := by
    have h : (Fm.D x i).R.m = 2 * (Fm.D x i).R.rS + 2 := by
      have h2 := (Fm.D x i).R.two_le_m
      obtain ⟨j, hj⟩ := (Fm.D x i).R.m_even
      unfold Formalism.BasicNotions.Ranks.rS
      omega
    exact_mod_cast h
  have hk3 : ((Fm.D x i).R.m : ℝ) + 3 ≤ (Fm.D x i).R.k := by exact_mod_cast (Fm.D x i).R.m_add_three_le_k
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have h2 := (Fm.D x i).R.two_le_m
    have h : 1 ≤ (Fm.D x i).R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hm4
    exact_mod_cast h
  have hL1 : (1 : ℝ) ≤ (Fm.L x i).sc.L := hLx x e9 i
  have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := by linarith
  have ha2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ (Fm.D x i).R.k := by
    have hM : 0 ≤ max C2 0 := le_max_right _ _
    have h1 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by
      have hp : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
      have hfl : (1 : ℝ) ≤ (Fm.D x i).R.f * (Fm.L x i).sc.L := one_le_mul_of_one_le_of_one_le hf1 hL1
      have h5 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by positivity
      calc ((Fm.D x i).R.m : ℝ) ^ 2 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := hp
        _ = ((Fm.D x i).R.m : ℝ) ^ 5 * 1 := by ring
        _ ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * ((Fm.D x i).R.f * (Fm.L x i).sc.L) := mul_le_mul_of_nonneg_left hfl h5
        _ = ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
    have h2 : C2 * ((Fm.D x i).R.m : ℝ) ^ 2 ≤
        max C2 0 * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (mul_le_mul_of_nonneg_left h1 hM)
    have h3 := hkx x e8 i
    calc C2 * ((Fm.D x i).R.m : ℝ) ^ 2 ≤
        max C2 0 * (((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L) := h2
      _ = max C2 0 * ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.D x i).R.f * (Fm.L x i).sc.L := by ring
      _ ≤ (Fm.D x i).R.k := h3
  have hcf : cF (Fm.D x i).R.f ≤ ((Fm.D x i).R.m : ℝ) := by
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hs : Real.sqrt ((Fm.D x i).R.rS : ℝ) ≤ ((Fm.D x i).R.rS : ℝ) := by
      have h1 : 1 ≤ Real.sqrt ((Fm.D x i).R.rS : ℝ) := Real.one_le_sqrt.mpr hr1
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((Fm.D x i).R.rS : ℝ) by linarith)
      nlinarith
    have hlf : Real.log ((Fm.D x i).R.f : ℝ) ≤ ((Fm.D x i).R.rS : ℝ) := le_trans hlogf hs
    unfold cF lg2f
    have hf0 : ((Fm.D x i).R.f : ℝ) ≠ 0 := ne_of_gt (by linarith)
    push_cast
    rw [Real.logb, Real.log_mul two_ne_zero hf0]
    have hq : (Real.log 2 + Real.log ((Fm.D x i).R.f : ℝ)) / Real.log 2 ≤ 1 + 2 * ((Fm.D x i).R.rS : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hr1p : (0 : ℝ) < ((Fm.D x i).R.rS : ℝ) + 1 := by linarith
  have hE1 : pairCountExponent (Fm.D x i) c (Fm.D x i).R.k =
      c * (((Fm.D x i).R.k : ℝ) + (Fm.D x i).R.m) * (Fm.D x i).R.m + c * cF (Fm.D x i).R.f := rfl
  have hbound := rows_q_bound (c := c) hmr (by linarith) hk3 (by linarith) hcf ha2
  obtain ⟨hTa, hTb, hTc⟩ := hT x hx i u u'
  obtain ⟨-, -, h23b, -, -, h24b, -, h26⟩ := hAmx x e4 i
  refine rows_RowsND_record (Y x hx i u u') (δ := 1) (δm := 1)
    (q := ⌈(((Fm.D x i).R.rS : ℝ) + 1) * (4 * (c * (Fm.D x i).R.k) + 4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k +
      4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) + C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 +
      12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2)⌉₊)
    { hH := hH
      hC3 := h20x x e1 i u u'
      hHH := rows_stHH_mono hc27 (by linarith) (h27x x e2 i u u')
      hV := rows_stVol_mono (Y x hx i u u') hcV (by linarith) (hVx x e3 i hx u u')
      hDEC := h26
      ha := h10a x i
      hb := h10bx x e7 i
      hp := h23b
      hpp := h24b
      h6 := h6x x e5 i
      hδ := zero_le_one
      hThA := h14 x i u u'
      hT := hTa
      hG0 := hTb
      hE := hTc
      hc := by linarith
      hCh := hCh
      hdim := rows_dim_pos (Y x hx i u u') hH0 (h8x x e6 i u u' hH)
      hq := ?_ } le_rfl hcC hC1 hCsq ?_
  · by_cases h0 : 0 ≤ (((Fm.D x i).R.rS : ℝ) + 1) * (4 * (c * (Fm.D x i).R.k) +
        4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k + 4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) +
        C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2)
    · have hcl := Nat.ceil_lt_add_one h0
      rw [hE1] at hcl ⊢
      linarith
    · rw [Nat.ceil_eq_zero.mpr (le_of_lt (not_le.mp h0))]
      push_cast
      exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (by positivity)
  · rw [le_div_iff₀ hr1p]
    have := Nat.le_ceil ((((Fm.D x i).R.rS : ℝ) + 1) * (4 * (c * (Fm.D x i).R.k) +
      4 * pairCountExponent (Fm.D x i) c (Fm.D x i).R.k + 4 * (c * ((Fm.D x i).R.rS : ℝ) ^ 2) +
      C2 * ((Fm.D x i).R.m : ℝ) ^ 2 / 2 + 12 * (((Fm.D x i).R.rS : ℝ) + 1) ^ 2))
    linarith

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
