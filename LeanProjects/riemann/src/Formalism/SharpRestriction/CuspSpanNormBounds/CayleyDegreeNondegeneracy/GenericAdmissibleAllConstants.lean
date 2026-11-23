import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericCountAllConstants

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem weak_numerical_bound (r f : ℕ) (NT G HH w0 cf lf C : ℝ) (hNT : 1 ≤ NT) (hNT2 : NT ^ 2 ≤ HH) (hG1 : 1 ≤ G)
    (hG : G ≤ HH) (hw0 : 0 ≤ w0) (hw : w0 * 9 ^ f ≤ HH) (hcf : 0 ≤ cf)
    (hE : 23 + cf + 3 * lf + 11 * r + 16 * (r : ℝ) ^ 2 ≤ C * (r : ℝ) ^ 2) :
    NT * G ^ cf * G * (w0 * HH ^ (11 + 3 * lf)) * positionCount r f 1 NT G HH ≤ HH ^ (C * (r : ℝ) ^ 2) := by
  have hH1 : 1 ≤ HH := hG1.trans hG
  have hH0 : 0 < HH := by linarith
  have hNT0 : 0 ≤ NT := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hNTle : NT ≤ HH := by nlinarith
  have h1 : NT ^ (2 * r) ≤ HH ^ r := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hNT2 r
  have h2 : G ^ r ≤ HH ^ r := pow_le_pow_left₀ hG0 hG r
  have h3 : G ^ cf ≤ HH ^ cf := Real.rpow_le_rpow hG0 hG hcf
  have h4 : w0 * 9 ^ (1 * f) ≤ HH := by simpa using hw
  have h5 : 0 ≤ w0 * 9 ^ (1 * f) := by positivity
  have hGc : 0 ≤ G ^ cf := Real.rpow_nonneg hG0 cf
  unfold positionCount
  set N : ℕ := 9 * 1 + 9 * 1 * r + 16 * r ^ 2 with hN
  have hNr : (N : ℝ) = 9 + 9 * (r : ℝ) + 16 * (r : ℝ) ^ 2 := by rw [hN]; push_cast; ring
  have hP : 0 ≤ HH ^ (11 + 3 * lf) := Real.rpow_nonneg hH0.le _
  calc NT * G ^ cf * G * (w0 * HH ^ (11 + 3 * lf)) * (NT ^ (2 * r) * G ^ r * 9 ^ (1 * f) * HH ^ N)
        = (NT * G ^ cf * G * HH ^ (11 + 3 * lf) * NT ^ (2 * r) * G ^ r) * (w0 * 9 ^ (1 * f)) * HH ^ N := by ring
    _ ≤ (HH * HH ^ cf * HH * HH ^ (11 + 3 * lf) * HH ^ r * HH ^ r) * HH * HH ^ N := by
        gcongr
    _ = HH ^ ((1 : ℝ) + cf + 1 + (11 + 3 * lf) + (r : ℝ) + (r : ℝ) + 1 + (N : ℝ)) := by
        simp only [Real.rpow_add hH0, Real.rpow_natCast, Real.rpow_one]
    _ ≤ HH ^ (C * (r : ℝ) ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hH1
        rw [hNr]; linarith

section SW

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def localGramProduct (Z : GramM D) : ℝ :=
  (∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

def sublatticesOfDet (L0 : LatticeW D) (j : ℕ) (G : ℝ) : Set (LatticeW D) :=
  {P | P ≤ L0 ∧ latticeRank D P = j ∧ latticeDetW D P = G}

def classWeightAlt : ℝ :=
  (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f

def GenericThetaWeak (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z →
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
    latticeRank D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
    latticeDetW D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = localGramProduct D u u' Z ∧
    1 ≤ localGramProduct D u u' Z ∧ localGramProduct D u u' Z ≤ HHZ D large₂.sc.b C Z

def SublatticeMeanBound (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ G HH : ℝ, 1 ≤ G → G ≤ HH → NT D u ≤ HH →
    MeanLe D F0 what₂ (fun Λ => (sublatticesOfDet D (L0X D Λ (lf D F0)) (D.R.k - 1) G).encard)
      (LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) * NT D u * G ^ (cF D.R.f) * G *
        (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))

def SameTermEquivalence : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    Equivalence (TEqv D Λ (lf D F0) : FlagU D u' → FlagU D u' → Prop)

theorem gram_equiv_refl {n : ℕ} (Z : Matrix (Fin n) (Fin n) D.host.E) : ZEquiv Z Z := by
  refine ⟨1, 1, fun a b h => Matrix.one_apply_ne h.ne, fun a => Matrix.one_apply_eq a,
    fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, ?_⟩
  rw [Matrix.map_one _ (by simp) (by simp)]
  simp

theorem generic_theta_of_weak {C' Cl Cg cb Cu cT CT C0 A C : ℝ}
    (h : GenericThetaWeak D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C) : GenericThetaSublattice D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro hH F0 he hz Λ hΛ F' hT hg hR
  obtain ⟨a, b, c, _, d⟩ := h hH F0 he hz Λ hΛ _ hR F' hT hg (gram_equiv_refl D _)
  exact ⟨a, b, (le_of_eq c).trans d⟩

theorem log_degree_bounds {C' Cl Cg cb Cu cT CT C0 A : ℝ} (hH : Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    0 ≤ Real.logb 2 D.R.f ∧ Real.logb 2 D.R.f ≤ 3 / 2 * (A * (D.R.rS : ℝ) ^ 2) ∧
      cF D.R.f = 2 + Real.logb 2 D.R.f := by
  obtain ⟨⟨hS, -, -⟩, -, -, -, -, -, hl, -⟩ := hH
  obtain ⟨-, -, hmf, -⟩ := hS
  have hm := D.R.two_le_m
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have h2 := Real.log_two_gt_d9
  have hlf := Real.log_nonneg hf
  have hb : Real.logb 2 D.R.f ≤ 3 / 2 * Real.log D.R.f := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨Real.logb_nonneg one_lt_two hf, by linarith, ?_⟩
  unfold cF lg2f
  rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  ring

theorem stSW_of {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hC : 52 + 6 * A ≤ C) (hCT : 2 * CT ≤ C ^ 2)
    (hW : ∀ Z : GramM D, classWeightAlt D * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z)
    (hE : SameTermEquivalence D u u')
    (h23 : TermPositionCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C)
    (hS : SublatticeMeanBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hG : GenericThetaWeak D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C) :
    UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro hH F0 he hz what₂ hrows Z hZ
  set XX : LatV D → Set (FlagU D u') := fun Λ =>
    {F' | IsTerm Λ (gS D) (lf D F0) F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) (lf D F0) F' ∧ ZEquiv (ZhatL (lf D F0) F') Z}
    with hXX
  have hcnt : ∀ Λ, cntSW D ((Tu D u' : ℕ) : D.host.E) (lf D F0) Λ Z = cntCl (XX Λ) (TEqv D Λ (lf D F0)) :=
    fun Λ => Formalism.MainNotions.S.Lem.Cnt.cntSW_eq D _ _ Λ Z
  by_cases hex : ∃ Λ ∈ what₂, (XX Λ).Nonempty
  · obtain ⟨Λ₀, hΛ₀, F₀, hF₀⟩ := hex
    obtain ⟨_, _, _, hG1, hGH⟩ := hG hH F0 he hz Λ₀ (hrows.1 Λ₀ hΛ₀) Z hZ F₀ ⟨hF₀.1, hF₀.2.1⟩ hF₀.2.2.1 hF₀.2.2.2
    set G := localGramProduct D u u' Z with hGdef
    set HH := HHZ D large₂.sc.b C Z with hHH
    have hH1 : 1 ≤ HH := one_le_gram_height D large₂ C Z
    have hNT1 := norm_T_pos D u
    have hNT2 : NT D u ^ 2 ≤ HH := norm_T_sq_le_gram_height D large₂ hH.1 u hCT Z
    have hNT : NT D u ≤ HH := by nlinarith
    have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have hv : 1 ≤ D.host.v := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
      exact h19
    have hn0 : 0 ≤ LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) := by
      unfold LatticeSumBounds.nTot
      have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
      have hpi := Real.pi_pos
      positivity
    have hw0 : 0 ≤ classWeightAlt D := by
      unfold classWeightAlt
      have hrd : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (d_rdE_pos hH.1).le _
      positivity
    have hG3 : G ≤ HH ^ 3 := by
      have : HH ≤ HH ^ 3 := by
        calc HH = HH ^ 1 := (pow_one _).symm
          _ ≤ HH ^ 3 := pow_le_pow_right₀ hH1 (by norm_num)
      linarith
    obtain ⟨hl0, hl1, hcF⟩ := log_degree_bounds D large₂ u u' hH
    have hr : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hH.2.1.1
    refine mean_le_of_mul D F0 what₂ _
      (fun Λ => (sublatticesOfDet D (L0X D Λ (lf D F0)) (D.R.k - 1) G).encard)
      (K := positionCount D.R.rS D.R.f 1 (NT D u) G HH) ?_ (hS hH F0 he hz what₂ hrows G HH hG1 hGH hNT) ?_ ?_
    · have : 0 ≤ HH ^ (11 + 3 * Real.logb 2 D.R.f) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ G ^ cF D.R.f := Real.rpow_nonneg (by linarith) _
      have h3 : 0 ≤ G := by linarith
      have h4 : 0 ≤ NT D u := by linarith
      positivity
    · intro Λ hΛ
      have hrow := hrows.1 Λ hΛ
      rw [hcnt Λ]
      refine class_count_fibres (XX Λ) _ (hE F0 Λ) (fun F' => latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) _ ?_ _ ?_
      · intro F' hF'
        obtain ⟨a, b, c, _, _⟩ := hG hH F0 he hz Λ hrow Z hZ F' ⟨hF'.1, hF'.2.1⟩ hF'.2.2.1 hF'.2.2.2
        exact ⟨a, b, c⟩
      · intro P hP
        have hsub : {a | a ∈ XX Λ ∧ latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) a) = P} ⊆
            termsOverSublattice D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z P := by
          rintro F' ⟨hF', hP'⟩
          exact ⟨⟨hF'.1, hF'.2.1⟩, hF'.2.2.2, hP'.ge⟩
        refine le_trans (ENat.toENNReal_le.2 (class_count_mono _ hsub)) ?_
        exact h23 hH F0 he hz Λ hrow Z hZ 1 le_rfl hk P hP.1 hP.2.1 G HH hG1 hP.2.2.le le_rfl hG3
    · rw [d_nProduct (u := u) (u' := u') hH.1 Z]
      have hnum := weak_numerical_bound D.R.rS D.R.f (NT D u) G HH (classWeightAlt D) (cF D.R.f) (Real.logb 2 D.R.f) C hNT1 hNT2 hG1
        hGH hw0 (hW Z) (by rw [hcF]; linarith) (by rw [hcF]; nlinarith)
      calc LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) * NT D u * G ^ cF D.R.f * G *
            (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)) * positionCount D.R.rS D.R.f 1 (NT D u) G HH
          = LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) * (NT D u * G ^ cF D.R.f * G *
            (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)) * positionCount D.R.rS D.R.f 1 (NT D u) G HH) := by ring
        _ ≤ LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) * HH ^ (C * (D.R.rS : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hnum hn0
        _ = _ := by rw [mul_comm]; rfl
  · refine mean_le_of_zero D F0 what₂ _ _ fun Λ hΛ => ?_
    rw [hcnt Λ]
    have hemp : XX Λ = ∅ := by
      by_contra hne
      exact hex ⟨Λ, hΛ, Set.nonempty_iff_ne_empty.2 hne⟩
    unfold cntCl
    rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    rintro O ⟨a, ha, _⟩
    rw [hemp] at ha
    exact ha

end SW

theorem logb_two_le_alt (x : ℝ) (hx : 1 ≤ x) : 0 ≤ Real.logb 2 x ∧ Real.logb 2 x ≤ 3 / 2 * Real.log x := by
  refine ⟨Real.logb_nonneg one_lt_two hx, ?_⟩
  have h2 := Real.log_two_gt_d9
  have hl := Real.log_nonneg hx
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

theorem sqrt_le_add_one (r : ℝ) (hr : 0 ≤ r) : Real.sqrt r ≤ r + 1 := by
  nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r, sq_nonneg (Real.sqrt r - 1)]

theorem log_factor_eq (f : ℕ) (hf : (1 : ℝ) ≤ f) : cF f = 2 + Real.logb 2 f := by
  unfold cF lg2f
  rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  ring

theorem base_numerical_le (k s b B : ℝ) (hb2 : 2 ≤ b) (hk0 : 0 ≤ k) (hkB : k ≤ B) (hs0 : 0 ≤ s) (hs : s ≤ b) :
    2 * k * s * 2 * 9 ≤ b ^ 7 * B := by
  have hB : 0 ≤ B := hk0.trans hkB
  have h64 : (2 : ℝ) ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ (by norm_num) hb2 6
  have hks : k * s ≤ B * b := mul_le_mul hkB hs hs0 hB
  have hBb : 0 ≤ B * b := mul_nonneg hB (by linarith)
  calc 2 * k * s * 2 * 9 = 36 * (k * s) := by ring
    _ ≤ 36 * (B * b) := by linarith
    _ ≤ b ^ 6 * (B * b) := by
        apply mul_le_mul_of_nonneg_right _ hBb
        norm_num at h64; linarith
    _ = b ^ 7 * B := by ring

section W0

variable (D : D7) (large₂ : SizeData₂ D)

theorem class_weight_le_pow {C' Cl Cg cb Cu cT CT C0 : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 1 ≤ Cl) :
    classWeightAlt D * 9 ^ D.R.f ≤ large₂.sc.b ^ ((10 + |Cg|) * (D.R.m : ℝ) * D.R.f) := by
  obtain ⟨_, _, h3, _, h5, _, _, _, _, _, h11, h12, h13, _, _, _, _, _, h19, _⟩ := h.1
  have h3' : D.R.m ^ 4 ≤ D.R.f := h3
  have h5' : Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.rS : ℝ) := h5
  have h11' : Real.log D.host.rdE ≤ large₂.sc.L / Cl := h11
  have h12' : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
  have h13' : (D.host.g 0 : ℝ) ≤ large₂.sc.b ^ Cg := h13
  have h19' : 1 ≤ D.host.v := h19
  have hL := d_one_le_L D large₂
  have hb2 := d_two_le_b D large₂
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hb0 : (0 : ℝ) < large₂.sc.b := by linarith
  have hm1 := one_le_m_alt D
  have hmeq : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by have := d_m_eq D; exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have hm : 1 ≤ D.R.m := by have := d_m_eq D; omega
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ hm
    exact_mod_cast le_trans this h3'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hrd1 : 1 ≤ D.host.rdE := by rw [hrd]; linarith
  have hrd0 : 0 < D.host.rdE := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := h11'.trans (div_le_self (by linarith) hCl)
    unfold Scale.b
    rw [← Real.exp_log hrd0]; exact Real.exp_le_exp.2 h1
  set B := large₂.sc.b ^ |Cg| with hB
  have hB1 : 1 ≤ B := Real.one_le_rpow hb1 (abs_nonneg _)
  have hkB : (D.R.k : ℝ) ≤ B := by
    have hkb : (1 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := one_le_mul_of_one_le_of_one_le hk1 hb1
    calc (D.R.k : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := le_mul_of_one_le_right (by linarith) hb1
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ hkb (by norm_num)
      _ ≤ large₂.sc.b ^ Cg := h12'.trans h13'
      _ ≤ B := Real.rpow_le_rpow_of_exponent_le hb1 (le_abs_self _)
  have hs : D.host.rdE ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    calc D.host.rdE ^ ((1 : ℝ) / 2) ≤ D.host.rdE ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hrd1 (by norm_num)
      _ = D.host.rdE := Real.rpow_one _
      _ ≤ _ := hrdb
  have hs0 : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hrd0.le _
  have hbase : 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) * 2 * 9 ≤ large₂.sc.b ^ ((7 : ℝ) + |Cg|) := by
    rw [Real.rpow_add hb0]
    have e7 : large₂.sc.b ^ (7 : ℝ) = large₂.sc.b ^ 7 := by exact_mod_cast Real.rpow_natCast large₂.sc.b 7
    rw [e7]
    exact base_numerical_le _ _ _ _ hb2 (by linarith) hkB hs0 hs

  have hfr : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [Formalism.MainNotions.StandardLattice.finrank_host D]; push_cast; ring
  have hdisc : |(discr D.host.E : ℝ)| = D.host.rdE ^ (2 * (D.R.f : ℝ)) := by
    unfold Host.rdE
    rw [hfr, ← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one]
  have hcFeq := log_factor_eq D.R.f hf1
  obtain ⟨hcF0, hlb⟩ := logb_two_le_alt (D.R.f : ℝ) hf1
  have hsq := sqrt_le_add_one (D.R.rS : ℝ) (Nat.cast_nonneg _)
  have hcF : cF D.R.f ≤ 3 * (D.R.m : ℝ) := by
    rw [hcFeq]; linarith
  have hh : (classNumber D.host.E : ℝ) ≤ large₂.sc.b ^ (3 * (D.R.m : ℝ) * D.R.f) := by
    have hc := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.classNumberBound D.host.E
    rw [hdisc, hfr, ← Real.rpow_mul hrd0.le] at hc
    have e : 2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2) = cF D.R.f * D.R.f := by
      unfold cF lg2f; ring
    rw [e] at hc
    have hcF1 : 0 ≤ cF D.R.f := by rw [hcFeq]; linarith
    calc (classNumber D.host.E : ℝ) ≤ D.host.rdE ^ (cF D.R.f * D.R.f) := hc
      _ ≤ large₂.sc.b ^ (cF D.R.f * D.R.f) := Real.rpow_le_rpow hrd0.le hrdb (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr)
  have hh0 : (0 : ℝ) ≤ (classNumber D.host.E : ℝ) := Nat.cast_nonneg _
  unfold classWeightAlt
  calc (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f
      = (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) * 2 * 9) ^ D.R.f * (classNumber D.host.E : ℝ) := by
        rw [mul_pow (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) * 2) 9,
          mul_pow (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) 2]; ring
    _ ≤ (large₂.sc.b ^ ((7 : ℝ) + |Cg|)) ^ D.R.f * large₂.sc.b ^ (3 * (D.R.m : ℝ) * D.R.f) := by
        gcongr
    _ = large₂.sc.b ^ (((7 : ℝ) + |Cg|) * D.R.f + 3 * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        have : 0 ≤ |Cg| := abs_nonneg _
        have hf0 : (0 : ℝ) ≤ D.R.f := by linarith
        have h7 : ((7 : ℝ) + |Cg|) * D.R.f ≤ ((7 : ℝ) + |Cg|) * ((D.R.m : ℝ) * D.R.f) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hf0 hm1) (by positivity)
        linarith

end W0

section SWF

variable {eps : ℝ} (Fm : FamP eps)

def SublatticeMeanFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', SublatticeMeanBound (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def GenericThetaWeakFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericThetaWeak (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

theorem generic_theta_family_of (Cg cb Cu cT CT C0 A : ℝ) (h : GenericThetaWeakFamily Fm Cg cb Cu cT CT C0 A) :
    GenericThetaFamily Fm Cg cb Cu cT CT C0 A := by
  obtain ⟨C₀, hC⟩ := h
  refine ⟨C₀, fun C hCC => ?_⟩
  obtain ⟨x0, hx⟩ := hC C hCC
  exact ⟨x0, fun x hx' i u u' => generic_theta_of_weak (Fm.D x i) (Fm.L x i) u u' (hx x hx' i u u')⟩

theorem generic_admissible_all_constants (hCl : 1 ≤ sCl Fm) (Cg cb Cu cT CT C0 A : ℝ)
    (hE : ∀ x (i : Fm.Ix x) u u', SameTermEquivalence (Fm.D x i) u u')
    (h23 : PositionCountFamilyGeneric Fm Cg cb Cu cT CT C0 A) (hS : SublatticeMeanFamily Fm Cg cb Cu cT CT C0 A)
    (hG : GenericThetaWeakFamily Fm Cg cb Cu cT CT C0 A) :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
      VanishingOnXAndXPlusMass.adm7 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C := by
  obtain ⟨C1, H1⟩ := h23
  obtain ⟨C2, H2⟩ := hG
  refine ⟨max (max C1 C2) (max (max 1 (52 + 6 * A)) (max CT (10 + |Cg|))), fun C hC => ?_⟩
  have hC1 : C1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC2 : C2 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC3 : 1 ≤ C := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hC
  have hC4 : 52 + 6 * A ≤ C := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hC
  have hC5 : CT ≤ C := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hC
  have hC6 : 10 + |Cg| ≤ C := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hC
  have hC7 : 10 ≤ C := by linarith [abs_nonneg Cg]
  obtain ⟨x0, H⟩ := ((H1 C hC1).and hS).and (H2 C hC2)
  refine ⟨x0, fun x hx i u u' => ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := H x hx i
  intro hH
  refine stSW_of _ _ u u' hC4 (by nlinarith) (fun Z => ?_) (hE x i u u') (a u u') (b u u') (c u u') hH
  exact (class_weight_le_pow _ _ hH.1 hCl).trans (scale_pow_le_gram_height _ _ (by nlinarith) Z)

theorem generic_admissible_family_of (hCl : 1 ≤ sCl Fm) (Cg cb Cu cT CT C0 A : ℝ)
    (hE : ∀ x (i : Fm.Ix x) u u', SameTermEquivalence (Fm.D x i) u u')
    (h23 : PositionCountFamilyGeneric Fm Cg cb Cu cT CT C0 A) (hS : SublatticeMeanFamily Fm Cg cb Cu cT CT C0 A)
    (hG : GenericThetaWeakFamily Fm Cg cb Cu cT CT C0 A) : VanishingOnXAndXPlusMass.adm7F Fm Cg cb Cu cT CT C0 A := by
  obtain ⟨C₀, hC⟩ := generic_admissible_all_constants Fm hCl Cg cb Cu cT CT C0 A hE h23 hS hG
  exact ⟨C₀, hC C₀ le_rfl⟩

end SWF

end Formalism.MainNotions.BridgeLemma₂

end
