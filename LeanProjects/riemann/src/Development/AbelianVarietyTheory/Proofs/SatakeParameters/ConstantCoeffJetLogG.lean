import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeProps

open MvPowerSeries GlobalTheory.ThStr Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem norm_eq_one_of_pow {n : ℕ} (hn : 0 < n) {a : ℂ_[l]} (ha : a ^ n = 1) : ‖a‖ = 1 := by
  have h : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn.ne').1 h

theorem norm_le_one_of_mem_Wp {w : ℂ_[l]} (hw : w ∈ Wp l) : ‖w‖ ≤ 1 := by
  have hc : IsClosed {x : ℂ_[l] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  refine closure_minimal (t := {x : ℂ_[l] | ‖x‖ ≤ 1}) (fun x hx => ?_) hc hw
  change ‖x‖ ≤ 1
  induction hx using Subring.closure_induction with
  | mem x hx => obtain ⟨n, hn, -, h⟩ := hx; exact (norm_eq_one_of_pow hn h).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem Wp_sub_Wfrac {w : ℂ_[l]} (hw : w ∈ Wp l) : w ∈ product_zeroth_first_parts.Wfrac l := by
  have h1 : (Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Set ℂ_[l]) ⊆
      (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := by
    have : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
        (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubring :=
      Subring.closure_le.2 (Algebra.subset_adjoin (R := ℚ_[l]) (s := product_zeroth_first_parts.rootsPrimeTo l))
    exact this
  have h2 := closure_mono h1 hw
  exact h2

theorem mem_Wint {w : ℂ_[l]} (hw : w ∈ Wp l) : w ∈ product_zeroth_first_parts.Wint l := ⟨Wp_sub_Wfrac hw, norm_le_one_of_mem_Wp hw⟩

theorem mem_Wfrac_of_inWf {x : ℂ_[l]} (hx : InWf x) : x ∈ product_zeroth_first_parts.Wfrac l := by
  obtain ⟨k, hk⟩ := hx
  have h := (product_zeroth_first_parts.Wfrac l).smul_mem (Wp_sub_Wfrac hk) ((l : ℚ_[l]) ^ k)⁻¹
  have hl0 : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, inv_mul_cancel_left₀ hl0] at h
  exact h

variable [NeZero d]

theorem parDeg_true_eq (n : ZMod d →₀ ℕ) : parDeg true n = (product_zeroth_first_parts.bideg d n).1 := by
  unfold parDeg product_zeroth_first_parts.bideg
  simp

theorem parDeg_false_eq (n : ZMod d →₀ ℕ) : parDeg false n = (product_zeroth_first_parts.bideg d n).2 := by
  unfold parDeg product_zeroth_first_parts.bideg
  congr 1
  funext s k
  by_cases h : Even s.val <;> simp [h]

theorem b1 {be : MvPowerSeries (ZMod d) ℂ_[l]} (h : IsBe d be) : product_zeroth_first_parts.B1 l d be :=
  fun m => mem_Wfrac_of_inWf (h.coef m)

theorem b2 {be : MvPowerSeries (ZMod d) ℂ_[l]} (h : IsBe d be) : product_zeroth_first_parts.B2 l d be := by
  intro u hu m
  have := congrArg (coeff m) (h.inv u hu)
  rw [coeff_rescale] at this
  rw [mul_comm]
  exact this

theorem b3 {be : MvPowerSeries (ZMod d) ℂ_[l]} (h : IsBe d be) : product_zeroth_first_parts.B3 l d be := by
  intro m hm
  obtain ⟨h1, h2, h3⟩ := h.bideg m hm
  rw [parDeg_true_eq] at h1 h3
  rw [parDeg_false_eq] at h2 h3
  refine ⟨h1, h2, fun he => h3 ?_⟩
  rw [he]
  exact ⟨rfl, rfl⟩

theorem constantCoeff_eq_zero {be : MvPowerSeries (ZMod d) ℂ_[l]} (h : IsBe d be) : constantCoeff be = 0 := by
  by_contra h0
  rw [← coeff_zero_eq_constantCoeff_apply] at h0
  have := (h.bideg 0 h0).1
  simp [parDeg] at this

def sideEmb (d : ℕ) : Bool × ZMod d ↪ ZMod d × Fin 2 :=
  ⟨fun c => (c.2, if c.1 then 1 else 0), by
    rintro ⟨a, b⟩ ⟨c, e⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    cases a <;> cases c <;> simp_all⟩

theorem constantCoeff_laS (s : ZMod d) : constantCoeff (laS l d s) = 0 :=
  (GlobalTheory.BiextInhab.laK_idMod2 (K := ℂ_[l]) (d := d) hl.out).1 s

theorem constantCoeff_laAt {κ : Type} [Finite κ] (ι : ZMod d → κ) (s : ZMod d) :
    constantCoeff (laAt (l := l) ι s) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (constantCoeff_laS s)

theorem constantCoeff_jetLogG (v : ZMod d × Fin 2) : constantCoeff (jetLogG l d v) = 0 := by
  rw [← GlobalTheory.BiextInhab.bridge l d v.2 v.1]
  exact constantCoeff_laAt _ _

theorem rename_laAt (c : Bool) (s : ZMod d) :
    rename (sideEmb d) (laAt (l := l) (fun r => (c, r)) s) = jetLogG l d (s, if c then (1 : Fin 2) else 0) := by
  have h1 : HasSubst (fun r : ZMod d => (X (c, r) : MvPowerSeries (Bool × ZMod d) ℂ_[l])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h2 : HasSubst (X ∘ sideEmb d : Bool × ZMod d → MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  rw [← GlobalTheory.BiextInhab.bridge l d _ s, rename_eq_subst, laAt, laAt, subst_comp_subst_apply h1 h2]
  congr 1
  funext r
  rw [subst_X h2]
  rfl

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

theorem expMv_eq_subst {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (PowerSeries.exp ℂ_[l]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem constantCoeff_expMv {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    constantCoeff (expMv G) = 1 := by
  rw [expMv_eq_subst hG, ← coeff_zero_eq_constantCoeff_apply, coeff_subst_range hG]
  simp

theorem subst_psubst {σ τ : Type} [Finite σ] {b : σ → MvPowerSeries τ ℂ_[l]} (hb : HasSubst b)
    {f : MvPowerSeries σ ℂ_[l]} (hf : constantCoeff f = 0) (g : PowerSeries ℂ_[l]) :
    subst b (PowerSeries.subst f g) = PowerSeries.subst (subst b f) g := by
  have ha : HasSubst (fun _ : Unit => f) := hasSubst_of_constantCoeff_zero fun _ => hf
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply ha hb]

theorem integralW_rename {F : MvPowerSeries (Bool × ZMod d) ℂ_[l]} (hF : IntegralW F) :
    IntegralW (rename (sideEmb d) F) := by
  intro m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (sideEmb d : Bool × ZMod d → ZMod d × Fin 2))
  · obtain ⟨n, rfl⟩ := hm
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    exact hF n
  · rw [coeff_rename_eq_zero _ _ hm]
    exact zero_mem _

theorem hasSubst_jet : HasSubst (jetLogG l d (β := Fin 2)) :=
  hasSubst_of_constantCoeff_zero constantCoeff_jetLogG

theorem hasSubst_side : HasSubst (X ∘ sideEmb d : Bool × ZMod d → MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_jet_subst (be : MvPowerSeries (ZMod d) ℂ_[l]) {a : ZMod d → MvPowerSeries (ZMod d × Fin 2) ℂ_[l]}
    {b : ZMod d → MvPowerSeries (Bool × ZMod d) ℂ_[l]} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (h : ∀ s, subst (jetLogG l d (β := Fin 2)) (a s) = rename (sideEmb d) (b s)) :
    subst (jetLogG l d (β := Fin 2)) (subst a be) = rename (sideEmb d) (subst b be) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hasSubst_jet, rename_eq_subst,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hasSubst_side]
  congr 1
  funext s
  rw [h s, rename_eq_subst]

theorem cc_subst {κ : Type} [Finite κ] {be : MvPowerSeries (ZMod d) ℂ_[l]} (hbe : constantCoeff be = 0)
    {a : ZMod d → MvPowerSeries κ ℂ_[l]} (ha : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a be) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha hbe

theorem overWOne_of_cob {be : MvPowerSeries (ZMod d) ℂ_[l]} (hbe : constantCoeff be = 0)
    {a₁ a₂ a₃ : ZMod d → MvPowerSeries (ZMod d × Fin 2) ℂ_[l]} {b₁ b₂ b₃ : ZMod d → MvPowerSeries (Bool × ZMod d) ℂ_[l]}
    (ha₁ : ∀ s, constantCoeff (a₁ s) = 0) (ha₂ : ∀ s, constantCoeff (a₂ s) = 0) (ha₃ : ∀ s, constantCoeff (a₃ s) = 0)
    (hb₁ : ∀ s, constantCoeff (b₁ s) = 0) (hb₂ : ∀ s, constantCoeff (b₂ s) = 0) (hb₃ : ∀ s, constantCoeff (b₃ s) = 0)
    (h₁ : ∀ s, subst (jetLogG l d (β := Fin 2)) (a₁ s) = rename (sideEmb d) (b₁ s))
    (h₂ : ∀ s, subst (jetLogG l d (β := Fin 2)) (a₂ s) = rename (sideEmb d) (b₂ s))
    (h₃ : ∀ s, subst (jetLogG l d (β := Fin 2)) (a₃ s) = rename (sideEmb d) (b₃ s))
    (hF : IntegralW (expMv (subst b₁ be - subst b₂ be - subst b₃ be))) :
    product_zeroth_first_parts.OverWOne l (subst (jetLogG l d (β := Fin 2)) (product_zeroth_first_parts.expS ℂ_[l] (subst a₁ be - subst a₂ be - subst a₃ be))) := by
  have hA : constantCoeff (subst a₁ be - subst a₂ be - subst a₃ be) = 0 := by
    rw [map_sub, map_sub, cc_subst hbe ha₁, cc_subst hbe ha₂, cc_subst hbe ha₃, sub_zero, sub_zero]
  have hB : constantCoeff (subst b₁ be - subst b₂ be - subst b₃ be) = 0 := by
    rw [map_sub, map_sub, cc_subst hbe hb₁, cc_subst hbe hb₂, cc_subst hbe hb₃, sub_zero, sub_zero]
  have e1 : subst (jetLogG l d (β := Fin 2)) (subst a₁ be - subst a₂ be - subst a₃ be) =
      rename (sideEmb d) (subst b₁ be - subst b₂ be - subst b₃ be) := by
    rw [subst_sub hasSubst_jet, subst_sub hasSubst_jet, map_sub, map_sub, subst_jet_subst be ha₁ hb₁ h₁,
      subst_jet_subst be ha₂ hb₂ h₂, subst_jet_subst be ha₃ hb₃ h₃]
  have e2 : subst (jetLogG l d (β := Fin 2)) (product_zeroth_first_parts.expS ℂ_[l] (subst a₁ be - subst a₂ be - subst a₃ be)) =
      rename (sideEmb d) (expMv (subst b₁ be - subst b₂ be - subst b₃ be)) := by
    rw [product_zeroth_first_parts.expS, subst_psubst hasSubst_jet hA, e1, rename_eq_subst, ← subst_psubst hasSubst_side hB,
      ← expMv_eq_subst hB, ← rename_eq_subst]
  rw [e2]
  refine ⟨fun m => mem_Wint (integralW_rename hF m), ?_⟩
  rw [constantCoeff_rename]
  exact constantCoeff_expMv hB

theorem rename_laAt0 (s : ZMod d) :
    rename (sideEmb d) (laAt (l := l) (fun r => (false, r)) s) = jetLogG l d (s, 0) := by
  simpa using rename_laAt (l := l) false s

theorem rename_laAt1 (s : ZMod d) :
    rename (sideEmb d) (laAt (l := l) (fun r => (true, r)) s) = jetLogG l d (s, 1) := by
  simpa using rename_laAt (l := l) true s

theorem b4 {be : MvPowerSeries (ZMod d) ℂ_[l]} (h : IsBe d be) : product_zeroth_first_parts.B4 l d be := by
  have hbe := constantCoeff_eq_zero h
  have hJ := hasSubst_jet (l := l) (d := d)
  have cX : ∀ v : ZMod d × Fin 2, constantCoeff (X v : MvPowerSeries (ZMod d × Fin 2) ℂ_[l]) = 0 :=
    fun _ => constantCoeff_X _
  have cL : ∀ (c : Bool) (s : ZMod d), constantCoeff (laAt (l := l) (fun r => (c, r)) s) = 0 :=
    fun c s => constantCoeff_laAt _ s
  refine ⟨?_, ?_⟩
  · refine overWOne_of_cob hbe ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (h.cob true)
    · intro s; split_ifs <;> simp
    · intro s; simp
    · intro s; split_ifs <;> simp
    · intro s; split_ifs <;> simp [cL]
    · intro s; exact cL false s
    · intro s; split_ifs <;> simp [cL]
    · intro s
      by_cases hs : Even s.val
      · simp only [hs, decide_true, if_true]
        rw [subst_add hJ, subst_X hJ, subst_X hJ, map_add, rename_laAt0, rename_laAt1]
      · simp only [hs, decide_false, if_false, Bool.false_eq_true]
        rw [subst_X hJ, rename_laAt0]
    · intro s
      rw [subst_X hJ, rename_laAt0]
    · intro s
      by_cases hs : Even s.val
      · simp only [hs, decide_true, if_true]
        rw [subst_X hJ, rename_laAt1]
      · simp only [hs, decide_false, if_false, Bool.false_eq_true]
        rw [subst_X hJ, rename_laAt0]
  · refine overWOne_of_cob hbe ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (h.cob false)
    · intro s; split_ifs <;> simp
    · intro s; simp
    · intro s; split_ifs <;> simp
    · intro s; split_ifs <;> simp [cL]
    · intro s; exact cL false s
    · intro s; split_ifs <;> simp [cL]
    · intro s
      by_cases hs : Even s.val
      · simp only [hs, decide_true, if_true, Bool.true_eq_false, if_false]
        rw [subst_X hJ, rename_laAt0]
      · simp only [hs, decide_false, if_false, if_true]
        rw [subst_add hJ, subst_X hJ, subst_X hJ, map_add, rename_laAt0, rename_laAt1]
    · intro s
      rw [subst_X hJ, rename_laAt0]
    · intro s
      by_cases hs : Even s.val
      · simp only [hs, decide_true, if_true, Bool.true_eq_false, if_false]
        rw [subst_X hJ, rename_laAt0]
      · simp only [hs, decide_false, if_false, if_true]
        rw [subst_X hJ, rename_laAt1]

theorem is_be_four_conditions : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d], Even d → ∀ be : MvPowerSeries (ZMod d) ℂ_[l],
    GlobalTheory.ThStr.IsBe d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be :=
  fun _ _ _ _ _ be h => ⟨b1 h, b2 h, b3 h, b4 h⟩

end GlobalTheory.BeProps
