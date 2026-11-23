import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithms
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLogStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupCocycleLthPowerCoboundaryModMaximalStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowAt.GoodInj

open GlobalTheory.RowLaw.CvEnd GlobalTheory.PlaceProj

variable {C : Type} [Field C] {V : VF C}

theorem mm_sum' {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f V.MM (fun _ _ => mm_add) mm_zero h

def ordIdeal (C : Type) [Field C] {τ : Type} (w : τ → ℕ) (n : ℕ) : Ideal (MvPowerSeries τ C) where
  carrier := {F | F ∈ ordGe C w n}
  add_mem' := fun ha hb => (ordGe C w n).add_mem ha hb
  zero_mem' := (ordGe C w n).zero_mem
  smul_mem' := fun c a ha => by
    have := ordGe_mul (ordGe_zero (w := w) c) ha
    rwa [zero_add] at this

theorem mem_ordIdeal {τ : Type} {w : τ → ℕ} {n : ℕ} {F : MvPowerSeries τ C} : F ∈ ordIdeal C w n ↔ F ∈ ordGe C w n :=
  Iff.rfl

theorem subst_congr_ord {σ τ : Type} {w : τ → ℕ} {n : ℕ} {a b : σ → MvPowerSeries τ C}
    (ha : MvPowerSeries.HasSubst a) (hb : MvPowerSeries.HasSubst b) (h : ∀ s, a s - b s ∈ ordGe C w n)
    (f : MvPowerSeries σ C) : MvPowerSeries.subst a f - MvPowerSeries.subst b f ∈ ordGe C w n := by
  intro e he
  rw [map_sub, MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst hb, sub_eq_zero]
  refine finsum_congr fun μ => ?_
  congr 1
  have h1 : (μ.prod fun s k => a s ^ k) - (μ.prod fun s k => b s ^ k) ∈ ordIdeal C w n := by
    rw [← Ideal.Quotient.eq]
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, Ideal.Quotient.eq.2 (mem_ordIdeal.2 (h s))]
  have h2 := mem_ordIdeal.1 h1 e he
  rwa [map_sub, sub_eq_zero] at h2

theorem mm_subst {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) (hi : ∀ s, IntS V (a s))
    {F : MvPowerSeries σ C} (hF : ∀ μ, V.MM (MvPowerSeries.coeff μ F)) (e : τ →₀ ℕ) :
    V.MM (MvPowerSeries.coeff e (MvPowerSeries.subst a F)) := by
  rw [MvPowerSeries.coeff_subst ha]
  refine finsum_induction (fun x => V.MM x) mm_zero (fun _ _ => mm_add) fun μ => ?_
  rw [smul_eq_mul, mul_comm]
  refine mm_mul ?_ (hF μ)
  revert e
  show IntS V _
  refine Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => ?_
  show IntS V (a s ^ μ s)
  induction μ s with
  | zero => rw [pow_zero]; exact intS_one
  | succ k ih => rw [pow_succ]; exact intS_mul ih (hi s)

theorem intS_X' {τ : Type} (s : τ) : IntS V (MvPowerSeries.X s : MvPowerSeries τ C) := by
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_add' {τ : Type} {F G : MvPowerSeries τ C} (hF : IntS V F) (hG : IntS V G) : IntS V (F + G) := fun e => by
  rw [map_add]; exact (hF e).add (hG e)

theorem intS_sub' {τ : Type} {F G : MvPowerSeries τ C} (hF : IntS V F) (hG : IntS V G) : IntS V (F - G) := fun e => by
  rw [map_sub]; exact (hF e).sub (hG e)

theorem intS_neg' {τ : Type} {F : MvPowerSeries τ C} (hF : IntS V F) : IntS V (-F) := fun e => by
  rw [map_neg]; exact (hF e).neg

section Chart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem formalAdd_const (H : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : κ) :
    MvPowerSeries.constantCoeff (addP Y a b i) = 0 :=
  constantCoeff_subst_zero (fun x => by
    rw [map_add, constantCoeff_subst_zero ha (lg_const H x), constantCoeff_subst_zero hb (lg_const H x), add_zero])
    (H.exc i)

theorem cob_root (H : RLaw Y V) {c : MvPowerSeries (Fin 2 × κ) C} (hc : IntS V c) {b : MvPowerSeries κ C}
    (hb : IntS V b) (hd : ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv C i b)))
    (h : ∀ μ, V.MM (MvPowerSeries.coeff μ (c ^ V.l + cob Y b))) :
    ∃ b' : MvPowerSeries κ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cob Y b')) := by
  haveI := H.closed
  obtain ⟨b', hb', hbb⟩ := (GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal C V κ).1 b hb hd
  obtain ⟨-, hroot, hfr⟩ := GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal C V (Fin 2 × κ)
  have s0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (gp_const (C := C) (κ := κ) (0 : Fin 2))
  have s1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (gp_const (C := C) (κ := κ) (1 : Fin 2))
  have sa := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (formalAdd_const H (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const (1 : Fin 2)))
  have i0 : ∀ s, IntS V (gp C κ (0 : Fin 2) s) := fun s => intS_X' _
  have i1 : ∀ s, IntS V (gp C κ (1 : Fin 2) s) := fun s => intS_X' _
  have hA := intS_subst sa H.addInt hb'
  have hB := intS_subst s0 i0 hb'
  have hD := intS_subst s1 i1 hb'
  have mA := mm_subst sa H.addInt hbb
  have mB := mm_subst s0 i0 hbb
  have mD := mm_subst s1 i1 hbb
  rw [MvPowerSeries.subst_sub sa, MvPowerSeries.subst_pow sa] at mA
  rw [MvPowerSeries.subst_sub s0, MvPowerSeries.subst_pow s0] at mB
  rw [MvPowerSeries.subst_sub s1, MvPowerSeries.subst_pow s1] at mD
  have e : cob Y (-b') = MvPowerSeries.subst (gp C κ (0 : Fin 2)) b' + MvPowerSeries.subst (gp C κ (1 : Fin 2)) b' -
      MvPowerSeries.subst (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1)) b' := by
    unfold cob
    rw [← MvPowerSeries.coe_substAlgHom sa, ← MvPowerSeries.coe_substAlgHom s0, ← MvPowerSeries.coe_substAlgHom s1,
      map_neg, map_neg, map_neg]
    ring
  refine ⟨-b', intS_neg' hb', ?_⟩
  rw [e]
  refine hroot _ _ hc (intS_sub' (intS_add' hB hD) hA) fun μ => ?_
  have k1 := (hfr _ _ (intS_add' hB hD) hA μ).2
  have k2 := (hfr _ _ hB hD μ).1
  have := mm_add (mm_add (mm_sub (mm_sub (mm_sub (h μ) k1) k2) (mA μ)) (mB μ)) (mD μ)
  convert this using 1
  simp only [cob, map_sub, map_add]
  ring

theorem ex_along (H : RLaw Y V) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : κ) :
    MvPowerSeries.subst (fun x => MvPowerSeries.subst a (Y.lg x)) (Y.ex i) = a i := by
  have hA := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have := MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (lg_const H)) hA (Y.ex i)
  rw [H.exlg, MvPowerSeries.subst_X hA] at this
  exact this.symm

theorem cvAt_const {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (cvAt s f) = 0 :=
  constantCoeff_subst_zero (σ := Unit) (fun _ => hs) hf

theorem subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (f : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) f = cvAt s (alongCv γ f) :=
  (MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (τ := Unit) hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs) f).symm

theorem cvAt_lin {N : ℕ} {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0) (h : ∀ n, 2 ≤ n → n < N → PowerSeries.coeff n f = 0) :
    cvAt s f - PowerSeries.coeff 1 f • s ∈ ordGe C (fun _ => 1) N := by
  have hS : MvPowerSeries.HasSubst (fun _ : Unit => s) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  have h1 : (f - PowerSeries.coeff 1 f • PowerSeries.X : MvPowerSeries Unit C) ∈ ordGe C (fun _ => 1) N := by
    intro e he
    have h2 : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [h2, Finsupp.weight_single, smul_eq_mul, mul_one] at he
    rw [h2]
    show PowerSeries.coeff (e ()) (f - PowerSeries.coeff 1 f • PowerSeries.X) = 0
    rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_X]
    rcases Nat.lt_trichotomy (e ()) 1 with h3 | h3 | h3
    · have : e () = 0 := by omega
      rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]; simp
    · rw [h3]; simp
    · rw [h _ h3 he, if_neg (by omega)]; simp
  have := ordGe_subst hS (fun _ => ordGe_one_of_const hs) h1
  rw [MvPowerSeries.subst_sub hS, MvPowerSeries.subst_smul hS] at this
  rwa [show MvPowerSeries.subst (fun _ : Unit => s) (PowerSeries.X : PowerSeries C) = s from
    MvPowerSeries.subst_X hS ()] at this

theorem additive_low (H : RLaw Y V) {N : ℕ} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (h : ∀ i n, 2 ≤ n → n < N → PowerSeries.coeff n (alongCv γ (Y.lg i)) = 0) (i : κ) :
    addP Y (fun j => cvAt (MvPowerSeries.X 0) (γ j)) (fun j => cvAt (MvPowerSeries.X 1) (γ j)) i -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i) ∈ ordGe C (fun _ => 1) N := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) C) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have cs : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add, c0, c1, add_zero]
  have hL : ∀ x, PowerSeries.constantCoeff (alongCv γ (Y.lg x)) = 0 := fun x =>
    constantCoeff_subst_zero (τ := Unit) hγ (lg_const H x)
  rw [← ex_along H (a := fun j => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j))
    (fun j => cvAt_const cs (hγ j)) i]
  unfold RowLaw.addP
  simp only [subst_cvAt c0 hγ, subst_cvAt c1 hγ, subst_cvAt cs hγ]
  refine subst_congr_ord (MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => ?_)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => cvAt_const cs (hL x)) (fun x => ?_) _
  · rw [map_add, cvAt_const c0 (hL x), cvAt_const c1 (hL x), add_zero]
  · have := Submodule.sub_mem _ (Submodule.add_mem _ (cvAt_lin c0 (hL x) (h x)) (cvAt_lin c1 (hL x) (h x)))
      (cvAt_lin cs (hL x) (h x))
    convert this using 1
    rw [smul_add]
    ring

theorem end_entry_int (H : RLaw Y V) {M : Matrix κ κ C}
    (hM : ∀ i, IntS V (endP Y M (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) (i j : κ) : V.Ge 0 (M i j) := by
  have h := matrixEnd_two (w := fun _ => 1) H M (b := (MvPowerSeries.X : κ → MvPowerSeries κ C))
    (fun i => MvPowerSeries.constantCoeff_X i) (fun i => ordGe_X (w := fun _ => 1) i) i (Finsupp.single j 1)
    (by simp [Finsupp.weight_single])
  rw [map_sub, sub_eq_zero, map_sum] at h
  have h2 := hM i (Finsupp.single j 1)
  rw [h] at h2
  simpa [MvPowerSeries.coeff_X, Finsupp.single_left_inj] using h2

theorem sg_sum (Y : RawChart C d I κ) {ι : Type} [Fintype ι] (b : ι → C) (v : ι → κ → C) :
    Y.sg (∑ c, b c • v c) = ∑ c, b c • Y.sg (v c) := by
  simp only [sg_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, smul_neg, Finset.smul_sum,
    smul_smul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

theorem coord_of_sat {g : Fin 2} {ww : κ → I g → C}
    (hw : ∀ c c' : I g, (c = c' → ∑ x, Y.u g c x * ww x c' = 1) ∧ (c ≠ c' → ∑ x, Y.u g c x * ww x c' = 0))
    (b : I g → C) (c' : I g) : ∑ x, (∑ c, b c * Y.u g c x) * ww x c' = b c' := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single c']
  · rw [(hw c' c').1 rfl, mul_one]
  · intro c _ hc
    rw [(hw c c').2 hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sg_all (H : RLaw Y V) (hP : HasProj Y V) {g : Fin 2} {γ : κ → PowerSeries C} (hγ : IsCv V γ)
    {A : I g → PowerSeries C} (hA : ∀ i, alongCv γ (Y.lg i) = ∑ c, Y.u g c i • A c)
    (h : ∀ q : I (1 - g), V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg (Y.u (1 - g) q)))))
    (v : κ → C) (hv : ∀ i, V.Ge 0 (v i)) : V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg v))) := by
  obtain ⟨M, h01, h10, hfix, -, hspan⟩ := hP
  have hE : IsEnd Y V (M g) (M (1 - g)) := by
    fin_cases g
    · exact h01
    · exact h10
  have hX : ∀ i : κ, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i : MvPowerSeries Unit C) = 0 := fun i => (hγ i).1
  have hΓ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (matrixEnd_const H (M g) hX)
  have hsg := Y.constantCoeff_sg (H.axes 0)
  have hK := (isCv_along hγ (f := fun _ : Unit =>
      MvPowerSeries.subst (endP Y (M g) (MvPowerSeries.X : κ → MvPowerSeries κ C)) (Y.sg v) -
        Y.sg ((M (1 - g)).mulVec v))
    (fun q => by rw [map_sub, constantCoeff_subst_zero (matrixEnd_const H (M g) hX) (hsg _), hsg, sub_self])
    (fun q => defect_int H hE hv) ()).2 V.l
  have hfixγ : ∀ i, endP Y (M g) (τ := Unit) γ i = γ i := by
    intro i
    rw [← ex_along H hγ0 i]
    unfold endP
    congr 1
    funext x
    have hA' : ∀ i, MvPowerSeries.subst γ (Y.lg i) = ∑ c, Y.u g c i • (A c : MvPowerSeries Unit C) := hA
    simp only [hA', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact congrFun (hfix g c) x
  obtain ⟨b, hb⟩ := hspan (1 - g) v
  obtain ⟨ww, hwi, hw⟩ := H.sat (1 - g)
  have hbi : ∀ c, V.Ge 0 (b c) := by
    intro c
    rw [← coord_of_sat hw b c]
    refine VF.Ge.sum fun x _ => VF.Ge.mul_int ?_ (hwi x c)
    have := congrFun hb x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact VF.Ge.sum fun y _ => (end_entry_int H hE.2.1 x y).mul_int (hv y)
  have e : alongCv γ (MvPowerSeries.subst (endP Y (M g) (MvPowerSeries.X : κ → MvPowerSeries κ C)) (Y.sg v) -
        Y.sg ((M (1 - g)).mulVec v)) =
      alongCv γ (Y.sg v) - ∑ c, b c • alongCv γ (Y.sg (Y.u (1 - g) c)) := by
    unfold alongCv
    rw [MvPowerSeries.subst_sub hΓ, MvPowerSeries.subst_comp_subst_apply hS hΓ, hb, sg_sum, subst_sum_smul hΓ]
    simp only [subst_endP H (M g) hγ0, hfixγ]
  beta_reduce at hK
  rw [e, map_sub, map_sum] at hK
  have := mm_add (mm_l_mul hK) (mm_sum' Finset.univ _ fun c _ => mm_mul (hbi c) (h c))
  convert this using 1
  simp only [PowerSeries.coeff_smul, smul_eq_mul, mul_sub, Finset.mul_sum]
  rw [sub_add, ← Finset.sum_sub_distrib, Finset.sum_eq_zero, sub_zero]
  intro c _
  ring

end Chart

theorem tangent_mm_of_nonDeg : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  intro C _ V d _ I _ κ _ Y H hP hN Hc _ g a _ w x hx hc0
  obtain ⟨⟨hT, hx0, -⟩, hx1⟩ := hx
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ : x ∈ Y.TySet V g := hT
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have tl : ∀ s : ℕ → C, PowerSeries.coeff V.l (tyS V.l s) = s 1 := fun s => by
    simpa using coeff_tyS_pow hl s 1
  have t1 : ∀ s : ℕ → C, PowerSeries.coeff 1 (tyS V.l s) = s 0 := fun s => by
    simpa using coeff_tyS_pow hl s 0
  have hlow : ∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (Y.lg i)) = 0 := by
    intro i n hn hn'
    rw [h1, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [PowerSeries.coeff_smul]
    by_cases hs : ∃ s, V.l ^ s = n
    · obtain ⟨s, rfl⟩ := hs
      have hs2 : s < 2 := (Nat.pow_lt_pow_iff_right (by omega)).1 hn'
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hn
      have : s = 1 := by omega
      rw [coeff_tyS_pow hl, this, hx1 c, smul_zero]
    · push Not at hs
      rw [coeff_tyS_of_ne _ _ hs, smul_zero]
  have hq : ∀ q : I (1 - g), V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg (Y.u (1 - g) q)))) := by
    intro q
    have e := congrArg (PowerSeries.coeff V.l) (h2 q)
    rw [tl, map_add, map_sub, map_sum, Finset.sum_eq_zero, add_zero] at e
    · have := mm_sub (mm_l_mul ((hlam q).2 V.l)) (hc0 q)
      convert this using 1
      unfold Cart.c0'
      rw [e]
      ring
    · intro c _
      split_ifs
      · rw [PowerSeries.coeff_smul, tl, hx1 c, smul_zero]
      · exact map_zero _
  obtain ⟨hbi, hbd⟩ := GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log C V d I κ Y H γ hγ hlow
  obtain ⟨hci, hcb⟩ := GlobalTheory.T.formalGroupCocycle_lthPower_coboundary_mod_maximal C V d I κ Y H γ hγ hlow
  have hcob := cob_root H hci hbi (hbd (sg_all H hP hγ h1 hq)) hcb
  have htan : ∀ i, V.MM (PowerSeries.coeff 1 (γ i)) := by
    by_contra hne
    push Not at hne
    refine hN γ hγ hne (fun i μ hμ0 hμ1 => ?_) hcob
    rw [additive_low H hγ0 hlow i μ]
    · exact mm_zero
    · rw [weight_one, Finsupp.degree_eq_sum, Fin.sum_univ_two]
      nlinarith
  have hco : ∀ i, PowerSeries.coeff 1 (γ i) = ∑ c, w c * Y.u g c i := by
    intro i
    have := lg_two (τ := Unit) (w := fun _ => 1) H (b := γ) hγ0 (fun i => ordGe_one_of_const (hγ0 i)) i
      (Finsupp.single () 1) (by simp [Finsupp.weight_single])
    have e : PowerSeries.coeff 1 (alongCv γ (Y.lg i) - γ i) = 0 := this
    rw [map_sub, sub_eq_zero, h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, t1, hx0, smul_eq_mul, mul_comm]
    rfl
  obtain ⟨ww, hwi, hw⟩ := H.sat g
  intro c
  rw [← coord_of_sat hw w c]
  refine mm_sum' _ _ fun i _ => ?_
  rw [← hco, mul_comm]
  exact mm_mul (hwi i c) (htan i)

end GlobalTheory.RowAt.GoodInj
