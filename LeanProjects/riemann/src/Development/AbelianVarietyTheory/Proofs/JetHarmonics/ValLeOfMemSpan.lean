import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DofIterSmulDir
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartEigenMemRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdLeadingMinors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdNabValLeadingMinorsOfColumnJets

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamGerm

namespace GlobalTheory.DepthBound

theorem minorMonomial_support {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ}
    (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (Z : T → Prop) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    {mo : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ} (hmo : mo ∈ (minorsP k col m).support) (l : Σ τ : T, Fin (r τ))
    (b : Fin n) (h : mo (l, b) ≠ 0) : Z l.1 ∧ ∃ i, col l.1 i = b := by
  have hS : minorsP k col m ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | Z x.1.1 ∧ ∃ i, col x.1.1 i = x.2} := by
    refine Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ => ?_
    by_cases hz : Z τ
    · exact Subalgebra.pow_mem _ (LeadingMinors.det_X_mem_supported _ _ fun a i => by exact ⟨hz, _, rfl⟩) _
    · rw [hm τ hz, pow_zero]; exact Subalgebra.one_mem _
  rw [MvPolynomial.mem_supported] at hS
  exact hS (Finset.mem_coe.2 ((MvPolynomial.mem_vars_iff_mem_support (l, b)).2
    ⟨mo, hmo, Finsupp.mem_support_iff.2 h⟩))

theorem map_minorsP {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) :
    MvPolynomial.map φ (minorsP k col m) = minorsP k' col m := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem eval_minorsP {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ)
    (y : (Σ τ : T, Fin (r τ)) × Fin n → k) :
    MvPolynomial.eval y (minorsP k col m) = ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) =>
      y (⟨τ, Fin.castLE s.isLt a⟩, col τ (Fin.castLE s.isLt i))).det ^ m τ s := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem minorMonomial_add (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m m' : ∀ τ, Fin (r τ) → ℕ) :
    minorsP k col (fun t s => m t s + m' t s) = minorsP k col m * minorsP k col m' := by
  simp only [minorsP, pow_add, Finset.prod_mul_distrib]

theorem sum_prod_restrict {k ι : Type} [CommRing k] [Fintype ι] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (ι × Fin n) k) (hP : ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S)
    (mu mu' : Fin n → (ι →₀ ℕ) → k) (h1 : ∀ mo ∈ P.support, ∀ b ∈ S, mu b (colM mo b) = mu' b (colM mo b))
    (h0 : ∀ b, b ∉ S → mu' b 0 = 1) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu' b (colM mo b) := by
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [Finset.prod_congr rfl (h1 mo hmo), Finset.prod_subset (Finset.subset_univ S)]
  intro b _ hb
  have : colM mo b = 0 := Finsupp.ext fun l => by
    by_contra h
    exact hb (hP mo hmo l b h)
  rw [this, h0 b hb]

section Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k] [Algebra ℚ k]
  [Algebra R k] (B : FB R d O) (h : PS k 2 d)

theorem nabVal_smul_dir (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (c : ι → k) (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) : B.nabVal k h w0 q f (fun l => c l • u l) (MvPolynomial.monomial mo 1) =
      (∏ l, c l ^ mo l) * B.nabVal k h w0 q f u (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one, DirScale.dmonOf_smul_dir, map_mul,
    constantCoeff_C]

theorem nabVal_C_mul (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : B.nabVal k h w0 q (C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold FB.nabVal
  rw [mul_assoc, GE.dpolyOf_Cmul_f, map_mul, constantCoeff_C]

theorem const_of_canon (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [WickVanishing.gt_const_ev_eq _ (WickVanishing.pair_points_zero_constant WickVanishing.gp_zero₂ (WickVanishing.gp_pt 0)), map_zero] at this

theorem nabVal_zero (hh : B.IsCanonGauge k h) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) : B.nabVal k h w0 q f u (MvPolynomial.monomial 0 1) = constantCoeff f := by
  have hA : ∀ b : O, WickVanishing.GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    WickVanishing.gt_const_ev _ (WickVanishing.pair_points_zero_constant (WickVanishing.gp_pt 0) (WickVanishing.gp_comp1 _ _ (hA w0) (WickVanishing.gp_pt 0))) h
      (const_of_canon B h hh)
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, ColumnValue.dmonOf_zero_index, map_mul,
    CrudeValue.constantCoeff_expS _ (by rw [WickVanishing.nt_const_smul, cL, mul_zero]), mul_one]

variable {R' : Type} [CommRing R'] [Algebra R' k] (φ : R →+* R') (hφ : (algebraMap R' k).comp φ = algebraMap R k)
include hφ

omit [Algebra ℚ k] in
theorem toK_map {n : ℕ} (f : PS R n d) : FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
  ext mo
  simp only [coeff_map, ← hφ, RingHom.comp_apply]

omit [Algebra ℚ k] in
theorem FK_map : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => toK_map φ hφ _

omit [Algebra ℚ k] in
theorem actK_map : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => toK_map φ hφ _

theorem isCanonGauge_map (hh : B.IsCanonGauge k h) : (FBMap.mapFB φ B).IsCanonGauge k h := by
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph1
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph2
  · exact (toK_map φ hφ _).trans hh.sy
  · rw [actK_map B φ hφ]; exact (toK_map φ hφ _).trans (hh.ad a)

omit [Algebra ℚ k] in
theorem hL_map : (FBMap.mapFB φ B).hL k h = B.hL k h := by
  funext w0; unfold FB.hL; rw [actK_map B φ hφ]

omit [Algebra ℚ k] in
theorem dAct_map : dAct k (FBMap.mapFB φ B) = dAct k B := by
  funext a; unfold dAct; rw [actK_map B φ hφ]

theorem nabVal_map (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (FBMap.mapFB φ B).nabVal k h w0 q f u P = B.nabVal k h w0 q f u P := by
  unfold FB.nabVal; rw [FK_map B φ hφ, hL_map B h φ hφ]

end Nab

section Val

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem mem_span_of_val_le (x y : TWO.Ov v) (hx : (x : F) ≠ 0) (h : v (x : F) ≤ v (y : F)) : y ∈ Ideal.span {x} := by
  have h0 : 0 ≤ v ((y : F) / x) := by
    by_contra hlt
    have e : v (y : F) = v ((y : F) / x) + v (x : F) := by rw [← v.map_mul, div_mul_cancel₀ _ hx]
    have hne : v (x : F) ≠ ⊤ := fun e' => hx (v.top_iff.1 e')
    have := WithTop.add_lt_add_right hne (not_le.1 hlt)
    rw [← e, zero_add] at this
    exact absurd h (not_le.2 this)
  refine Ideal.mem_span_singleton'.2 ⟨⟨(y : F) / x, h0⟩, Subtype.ext ?_⟩
  exact div_mul_cancel₀ _ hx

theorem val_le_of_mem_span {x y : TWO.Ov v} (h : y ∈ Ideal.span {x}) : v (x : F) ≤ v (y : F) := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [Subring.coe_mul, v.map_mul]
  exact le_add_of_nonneg_left (TWO.v_nonneg v c)

theorem val_prod_le {κ : Type} (S : Finset κ) (x : κ → F) (r : κ → ℚ) (h : ∀ k ∈ S, v (x k) ≤ (r k : ℚ)) :
    v (∏ k ∈ S, x k) ≤ ((∑ k ∈ S, r k : ℚ) : WithTop ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, v.map_mul, WithTop.coe_add]
    exact add_le_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Val

theorem val_eigen_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (φ : R →+* TWO.Ov v)
    (hφ : (algebraMap (TWO.Ov v) F).comp φ = algebraMap R F) (B : FB R d O) (h : PS F 2 d) (hh : B.IsCanonGauge F h)
    (w0 a : O) (p k : ℕ) (hp0 : p ≠ 0) (hp : ¬ IsUnit (p : TWO.Ov v)) (hcop : ∃ u u' : O, u * a + u' * star a = 1)
    (ω : PS R 1 d) (hω1 : constantCoeff ω = 1)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ (c : O) l, (dAct F B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → τ t a ∈ Ideal.span {(p : TWO.Ov v)})
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v) (f : Fin n → PS (TWO.Ov v) 1 d)
    (hf0 : ∀ b ∈ S, v (constantCoeff (FB.toK F (f b))) = 0)
    (hf : ∀ b ∈ S, ∀ l, Z l.1 → ∀ mo, v (p : F) ≤ v (coeff mo (Dof (B.FK F) (fun i => (e l i : F)) (FB.toK F (f b)) -
      C (yy (l, b) : F) * FB.toK F (f b))))
    (γ ep : ℚ) (hep : v (p : F) = (ep : ℚ))
    (hy : ∀ t, Z t → ∀ s : Fin (rk t), v (((Matrix.of fun a i : Fin (s.val + 1) =>
      yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov v) : F) ≤ ((s.val + 1) * γ : ℚ))
    (hD : (∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ < ep) :
    v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
      B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial (colM mo b) 1)) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
  classical
  have hpF : ((p : TWO.Ov v) : F) = p := map_natCast (TWO.Ov v).subtype p
  have hmax : ∀ x ∈ Ideal.span {(p : TWO.Ov v)}, x ∈ IsLocalRing.maximalIdeal (TWO.Ov v) :=
    fun x hx => (Ideal.span_singleton_le_iff_mem _).2 hp hx
  let e₁ : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l => if Z l.1 then e l else 0
  let α : (Σ t, Fin (rk t)) → TWO.Ov v := fun l => if Z l.1 then τ l.1 a else 0
  let y₁ : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v := fun x => if Z x.1.1 ∧ x.2 ∈ S then yy x else 0
  let f₁ : Fin n → PS (TWO.Ov v) 1 d := fun b => if b ∈ S then f b else 1
  have hB' := isCanonGauge_map B h φ hφ hh
  obtain ⟨ρ, hρ, hval⟩ := nabVal_columns_congr (TWO.Ov v) d O F (FBMap.mapFB φ B) h hB' w0 a p k
    (MvPowerSeries.map φ ω) (by rw [toK_map φ hφ, actK_map B φ hφ, hL_map B h φ hφ, hω])
    (Ideal.span {(p : TWO.Ov v)}) _ e₁ α
    (fun l => by
      by_cases hl : Z l.1
      · simpa only [α, if_pos hl] using hZ _ hl
      · simp only [α, if_neg hl]; exact Ideal.zero_mem _)
    (fun l => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · simp only [e₁, α, if_pos hl]; exact he a l
      · simp only [e₁, α, if_neg hl, Pi.zero_apply, map_zero, zero_smul]
        exact Matrix.mulVec_zero _)
    (fun l l' => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · by_cases hl' : Z l'.1
        · simp only [e₁, if_pos hl, if_pos hl']
          obtain ⟨u, u', huu⟩ := hcop
          have h1 : τ l'.1 (star a) ∉ IsLocalRing.maximalIdeal (TWO.Ov v) := fun hx => by
            have := congrArg (τ l'.1) huu
            rw [map_add, map_mul, map_mul, map_one] at this
            exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 (this ▸
              Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmax _ (hZ _ hl'))) (Ideal.mul_mem_left _ _ hx)))
          have h2 : IsUnit (τ l.1 a - τ l'.1 (star a)) := by
            by_contra hx
            have := Ideal.sub_mem _ (hmax _ (hZ _ hl)) ((IsLocalRing.mem_maximalIdeal _).2 hx)
            rw [sub_sub_cancel] at this
            exact h1 this
          have h3 := bilinPart_eigen_mem_range (TWO.Ov v) d O F _ h hB' a (e l) (e l') _ _
            (by rw [dAct_map B φ hφ]; exact he a l) (by rw [dAct_map B φ hφ]; exact he (star a) l') h2
          have h4 := he w0 l'
          change (dAct F B w0).mulVec (fun i => algebraMap (TWO.Ov v) F (e l' i)) =
            algebraMap (TWO.Ov v) F (τ l'.1 w0) • fun i => algebraMap (TWO.Ov v) F (e l' i) at h4
          rw [h4, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
          exact Subring.mul_mem _ ⟨_, rfl⟩ h3
        · simp only [e₁, if_neg hl', Pi.zero_apply, map_zero]
          rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]
          exact Subring.zero_mem _
      · simp only [e₁, if_neg hl, Pi.zero_apply, map_zero]
        rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, zero_dotProduct]
        exact Subring.zero_mem _)
    n f₁ y₁
    (fun l b mo => by
      by_cases hl : Z l.1
      · by_cases hb : b ∈ S
        · refine mem_span_of_val_le v _ _ (by rw [hpF]; exact_mod_cast hp0) ?_
          rw [hpF]
          refine (hf b hb l hl mo).trans_eq (congrArg v ?_)
          simp only [e₁, f₁, y₁, if_pos hl, if_pos hb, if_pos (And.intro hl hb)]
          change _ = algebraMap (TWO.Ov v) F (coeff mo (Dof (FBMap.mapFB φ B).G.F (e l) (f b) - C (yy (l, b)) * f b))
          rw [← coeff_map]
          refine congrArg (coeff mo) (Eq.symm ?_)
          rw [map_sub, map_mul, map_C, InvDerMap.map_Dof, ← FK_map B φ hφ]
          rfl
        · simp [f₁, y₁, hb, Dof]
      · simp [e₁, y₁, hl, Dof])
    (minorsP (TWO.Ov v) col m)
  have hinj : Function.Injective (algebraMap (TWO.Ov v) F) := Subtype.val_injective
  rw [sum_prod_restrict S (minorsP F col m) (fun mo hmo l b hb => by
      obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
      exact hS _ i hz)
    (fun b mo => B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial mo 1))
    (fun b mo => (FBMap.mapFB φ B).nabVal F h w0 (p * k) (FB.toK F (f₁ b * MvPowerSeries.map φ ω ^ k))
      (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      have e1 : (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) =
          fun l => (if Z l.1 then (1 : F) else 0) • fun i => (e l i : F) := by
        funext l i
        by_cases hl : Z l.1 <;> simp [e₁, hl]
      have e2 : ∏ l, (if Z l.1 then (1 : F) else 0) ^ colM mo b l = 1 := Finset.prod_eq_one fun l _ => by
        by_cases hl : Z l.1
        · rw [if_pos hl, one_pow]
        · have : colM mo b l = 0 := by
            by_contra hx
            exact hl (minorMonomial_support col m Z hm hmo l b hx).1
          rw [this, pow_zero]
      beta_reduce
      rw [nabVal_map B h φ hφ, e1, nabVal_smul_dir, e2, one_mul, mul_comm p k, FB.toK, FB.toK, FB.toK, map_mul, map_pow,
        ← FB.toK, ← FB.toK, ← FB.toK, ← FB.toK, toK_map φ hφ]
      simp only [f₁, if_pos hb])
    (fun b hb => by
      beta_reduce
      rw [nabVal_zero _ h hB']
      simp [f₁, hb, hω1])]
  rw [← map_minorsP (algebraMap (TWO.Ov v) F), MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hval, map_add]
  have hmain : v (algebraMap (TWO.Ov v) F (MvPolynomial.eval y₁ (minorsP (TWO.Ov v) col m) *
      ∏ b, constantCoeff (f₁ b))) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
    rw [map_mul, v.map_mul, map_prod, eval_minorsP, map_prod]
    refine (add_le_add (val_prod_le v _ _ (fun t => ∑ s : Fin (rk t), (m t s * (s.val + 1) : ℕ) * γ) fun t _ => ?_)
      (val_prod_le v _ _ (fun _ => 0) fun b _ => ?_)).trans (le_of_eq ?_)
    · rw [map_prod]
      refine val_prod_le v _ _ _ fun s _ => ?_
      rw [map_pow, v.map_pow]
      by_cases ht : Z t
      · have e3 : (Matrix.of fun a i : Fin (s.val + 1) =>
            y₁ (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))) = Matrix.of fun a i : Fin (s.val + 1) =>
            yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i)) := by
          ext1 a i
          exact if_pos ⟨ht, hS _ _ ht⟩
        rw [e3]
        refine (nsmul_le_nsmul_right (hy t ht s) _).trans (le_of_eq ?_)
        rw [← WithTop.coe_nsmul]
        congr 1
        push_cast
        ring
      · simp [hm t ht]
    · by_cases hb : b ∈ S
      · have := hf0 b hb
        rw [constantCoeff_map] at this
        simp only [f₁, if_pos hb, this]
        rfl
      · simp [f₁, hb]
    · rw [← WithTop.coe_add]
      congr 1
      simp [Finset.sum_mul]
  have hρ' : ((ep : ℚ) : WithTop ℚ) ≤ v (algebraMap (TWO.Ov v) F ρ) := by
    rw [← hep, ← hpF]; exact val_le_of_mem_span v hρ
  rw [v.map_add_eq_of_lt_left (lt_of_le_of_lt hmain (lt_of_lt_of_le (by exact_mod_cast hD) hρ'))]
  exact hmain

theorem val_factorial {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {p n : ℕ} (hp : p.Prime)
    (hpu : ¬ IsUnit (p : TWO.Ov v)) (hn : n < p) : v (n.factorial : F) = 0 := by
  have h1 : IsCoprime ((n.factorial : ℤ) : TWO.Ov v) ((p : ℤ) : TWO.Ov v) :=
    (Nat.isCoprime_iff_coprime.2 (hp.coprime_factorial_of_lt hn).symm).intCast
  obtain ⟨a, b, hab⟩ := h1
  have h2 : IsUnit ((n.factorial : ℕ) : TWO.Ov v) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact_mod_cast isUnit_of_mul_isUnit_right h
    · exact absurd (by exact_mod_cast isUnit_of_mul_isUnit_right h) hpu
  have h3 := TWO.v_unit v h2.unit
  rwa [IsUnit.unit_spec, show (((n.factorial : ℕ) : TWO.Ov v) : F) = n.factorial from
    map_natCast (TWO.Ov v).subtype _] at h3

theorem val_unit_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (B : FB R d O) (h : PS F 2 d)
    (hh : B.IsCanonGauge F h) (w0 a : O) (p k : ℕ) (hp' : p.Prime) (hp : ¬ IsUnit (p : TWO.Ov v)) (ω : PS R 1 d)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ l, (dAct F B a).mulVec (fun i => (e l i : F)) = (τ l.1 a : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → IsUnit (τ t a)) (lam : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (hlam : ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0)
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hcol : ∀ t, Function.Injective (col t))
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (hD : ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) < p) :
    ∃ (g : Fin n → PS F 1 d) (nb : Fin n → ℕ), (∀ b mo, 0 ≤ v (coeff mo (g b))) ∧
      ∑ b, nb b = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) ∧ ∀ f : Fin n → PS F 1 d,
      (∀ b ∈ S, ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ nb b → coeff mo (f b) = coeff mo (g b)) →
      v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
        B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
          (MvPolynomial.monomial (colM mo b) 1)) = 0 := by
  classical
  let sc : (Σ t, Fin (rk t)) → (TWO.Ov v)ˣ := fun l => if hl : Z l.1 then (hZ _ hl).unit else 1
  let lam' : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l i => ((sc l)⁻¹ : (TWO.Ov v)ˣ) * lam l i
  let u' : (Σ t, Fin (rk t)) → Fin d → F := fun l => ((sc l : TWO.Ov v) : F) • fun i => (e l i : F)
  obtain ⟨al, hal⟩ : ∃ al : (Σ t, Fin (rk t)) × Fin n →₀ ℕ, al = ∑ τ, ∑ s : Fin (rk τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (rk τ)),
      col τ (Fin.castLE s.isLt a)) 1 := ⟨_, rfl⟩
  obtain ⟨hc1, -, hdeg, -⟩ := LeadingMinors.coeff_prod_leading_minors F T rk n col m hcol (minorsP F col m) al rfl hal
  have hsup : al ∈ (minorsP F col m).support := MvPolynomial.mem_support_iff.2 (by rw [hc1]; exact one_ne_zero)
  have hcols : ∀ mo ∈ (minorsP F col m).support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S := fun mo hmo l b hb => by
    obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
    exact hS _ i hz
  let g : Fin n → PS F 1 d := fun b =>
    ∏ l, (∑ i, C (lam' l i : F) * (X ((0 : Fin 1), i) : PS F 1 d)) ^ al (l, b)
  refine ⟨g, fun b => (colM al b).degree, fun b mo => ?_, (SymbolCols.sum_degree_colM al).trans hdeg, fun f hf => ?_⟩
  · have : g b = MvPowerSeries.map (algebraMap (TWO.Ov v) F)
        (∏ l, (∑ i, C (lam' l i) * (X ((0 : Fin 1), i) : PS (TWO.Ov v) 1 d)) ^ al (l, b)) := by
      simp only [map_prod, map_pow, map_sum, map_mul, map_C, map_X]
      rfl
    rw [this, coeff_map]
    exact TWO.v_nonneg v _
  let f₂ : Fin n → PS F 1 d := fun b => if b ∈ S then f b else g b
  have key := sum_prod_nabVal_leading_minors_of_column_jets R d O F B h (const_of_canon B h hh) w0 k T rk n col m hcol
    (minorsP F col m) al rfl hal u' (fun _ l i => (lam' l i : F)) (fun b l l' _ _ => by
      have h1 : ∑ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) = if l = l' then 1 else 0 := by
        have : ∀ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) =
            (((sc l)⁻¹ : (TWO.Ov v)ˣ) * (sc l' : TWO.Ov v)) * (lam l i * e l' i) := fun i => by
          simp only [lam']; ring
        simp only [this]
        rw [← Finset.mul_sum, hlam]
        split_ifs with hl
        · rw [hl, Units.inv_mul, mul_one]
        · rw [mul_zero]
      have h2 := congrArg (algebraMap (TWO.Ov v) F) h1
      rw [map_sum, apply_ite (algebraMap (TWO.Ov v) F), map_one, map_zero] at h2
      exact h2)
    (fun _ => 1) f₂ (fun b mo hmo => by
      rw [one_mul]
      by_cases hb : b ∈ S
      · simp only [f₂, if_pos hb]; exact hf b hb mo hmo
      · simp only [f₂, if_neg hb]; rfl)
  rw [sum_prod_restrict S (minorsP F col m) hcols
    (fun b mo => B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
      (MvPolynomial.monomial mo 1))
    (fun b mo => B.nabVal F h w0 k (f₂ b) u' (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      beta_reduce
      rw [mul_comm k p, nabVal_pullback_monomial R d O F B h hh w0 a p k ω hω _ _ (fun l => (τ l.1 a : F)) he,
        nabVal_smul_dir]
      simp only [f₂, if_pos hb]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : Z l.1
      · simp only [sc, dif_pos hl, IsUnit.unit_spec]
      · have : colM mo b l = 0 := by
          by_contra hx
          exact hl (minorMonomial_support col m Z hm hmo l b hx).1
        rw [this, pow_zero, pow_zero])
    (fun b hb => by
      beta_reduce
      have h0 : ∀ l, al (l, b) = 0 := fun l => by
        by_contra hx
        exact hb (hcols al hsup l b hx)
      rw [nabVal_zero _ h hh]
      simp only [f₂, if_neg hb, g, h0, pow_zero, Finset.prod_const_one, map_one]), key, Finset.prod_const_one, one_mul]
  refine Finset.prod_induction _ (fun x => v x = 0) (fun x x' hx hx' => by rw [v.map_mul, hx, hx', add_zero])
    v.map_one fun x _ => val_factorial v hp' hp (lt_of_le_of_lt (Finsupp.le_degree x al) (hdeg ▸ hD))

end GlobalTheory.DepthBound
