import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la}

lemma nval_neg' {T : CDVR} (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    simp only [vV, Valuation.map_neg]

variable (hs : ∀ ζ, SecPt ζ (y ζ))

def liftC (ζ : PtsG G la) : Lc (xplus X E hM) la G.w →+* (hs ζ).T.Fr :=
  IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) (S := Lc (xplus X E hM) la G.w) (hs ζ).s0

lemma liftC_eq (ζ : PtsG G la) (x : Lc (xplus X E hM) la G.w) : liftC hs ζ x = (hs ζ).lift x := rfl

lemma liftC_alg (ζ : PtsG G la) (r : Rp (xplus X E hM) la G.N) :
    liftC hs ζ (algebraMap (Rp (xplus X E hM) la G.N) (Lc (xplus X E hM) la G.w) r) = (hs ζ).ev r :=
  IsLocalization.lift_eq _ r

def locSub : Submonoid (Lc (xplus X E hM) la G.w) where
  carrier := {x | ∀ ζ, liftC hs ζ x ≠ 0}
  mul_mem' := fun {a b} ha hb ζ => by
    show liftC hs ζ (a * b) ≠ 0
    rw [map_mul]; exact mul_ne_zero (ha ζ) (hb ζ)
  one_mem' := fun ζ => by
    show liftC hs ζ 1 ≠ 0
    rw [map_one]; exact one_ne_zero

abbrev LamL : Type := Localization (locSub hs)

def ιL : Lc (xplus X E hM) la G.w →+* LamL hs := algebraMap (Lc (xplus X E hM) la G.w) (LamL hs)

def tayL : LamL hs →+* MvPowerSeries (Idx D j G.N) (LamL hs) :=
  Tay.loc (locSub hs) (LamL hs) (tayLc (xplus X E hM) la G.w) (tayLc_isTay _ _ _)

def hdL (β : Idx D j G.N →₀ ℕ) : LamL hs →+ LamL hs := Tay.co (tayL hs) β

lemma hdL_zero (x : LamL hs) : hdL hs 0 x = x := Tay.co_zero (Tay.loc_isTay _ _ _ _) x

lemma hdL_ι (β : Idx D j G.N →₀ ℕ) (x : Lc (xplus X E hM) la G.w) :
    hdL hs β (ιL hs x) = ιL hs (hasse (xplus X E hM) la G.w β x) := by
  unfold hdL ιL tayL
  rw [Tay.loc_co]
  rfl

lemma hdL_mul (β : Idx D j G.N →₀ ℕ) (x z : LamL hs) :
    hdL hs β (x * z) = ∑ q ∈ antidiagonal β, hdL hs q.1 x * hdL hs q.2 z := Tay.co_mul _ β x z

lemma hdL_one (β : Idx D j G.N →₀ ℕ) : hdL hs β 1 = if β = 0 then 1 else 0 := by
  show MvPowerSeries.coeff β (tayL hs 1) = _
  rw [map_one, MvPowerSeries.coeff_one]

def evL (ζ : PtsG G la) : LamL hs →+* (hs ζ).T.Fr :=
  IsLocalization.lift (M := locSub hs) (g := liftC hs ζ) (fun m => IsUnit.mk0 _ (m.2 ζ))

lemma evL_ι (ζ : PtsG G la) (x : Lc (xplus X E hM) la G.w) : evL hs ζ (ιL hs x) = liftC hs ζ x :=
  IsLocalization.lift_eq _ _

def hdList : List (Idx D j G.N →₀ ℕ) → LamL hs → LamL hs
  | [] => id
  | β :: l => fun x => hdL hs β (hdList l x)

lemma hdList_nil (x : LamL hs) : hdList hs [] x = x := rfl

lemma hdList_cons (β : Idx D j G.N →₀ ℕ) (l : List (Idx D j G.N →₀ ℕ)) (x : LamL hs) :
    hdList hs (β :: l) x = hdL hs β (hdList hs l x) := rfl

lemma hdList_add (l : List (Idx D j G.N →₀ ℕ)) (x z : LamL hs) :
    hdList hs l (x + z) = hdList hs l x + hdList hs l z := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [hdList_cons, hdList_cons, hdList_cons, ih, map_add]

lemma hdList_zero (l : List (Idx D j G.N →₀ ℕ)) : hdList hs l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [hdList_cons, ih, map_zero]

lemma hdList_neg (l : List (Idx D j G.N →₀ ℕ)) (x : LamL hs) : hdList hs l (-x) = -hdList hs l x := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [hdList_cons, hdList_cons, ih, map_neg]

lemma hdList_one (l : List (Idx D j G.N →₀ ℕ)) : hdList hs l 1 = 0 ∨ hdList hs l 1 = 1 := by
  induction l with
  | nil => exact Or.inr rfl
  | cons β l ih =>
    rw [hdList_cons]
    rcases ih with h | h
    · left; rw [h, map_zero]
    · rw [h, hdL_one]; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

lemma hdList_append (l : List (Idx D j G.N →₀ ℕ)) (β : Idx D j G.N →₀ ℕ) (x : LamL hs) :
    hdList hs l (hdL hs β x) = hdList hs (l ++ [β]) x := by
  induction l with
  | nil => rfl
  | cons γ l ih => rw [List.cons_append, hdList_cons, hdList_cons, ih]

def IntAllL (x : LamL hs) : Prop := ∀ ζ, 0 ≤ nval (hs ζ).T.V 1 (evL hs ζ x)

lemma intAll_zero : IntAllL hs 0 := fun ζ => by rw [map_zero, nval_zero]; exact le_top

lemma intAll_one : IntAllL hs 1 := fun ζ => by
  rw [map_one, nval_of_ne one_ne_zero, vV_one']; simp

lemma intAll_add {x z : LamL hs} (hx : IntAllL hs x) (hz : IntAllL hs z) : IntAllL hs (x + z) := fun ζ => by
  rw [map_add]; exact (le_min (hx ζ) (hz ζ)).trans (nval_add 1 _ _)

lemma intAll_mul {x z : LamL hs} (hx : IntAllL hs x) (hz : IntAllL hs z) : IntAllL hs (x * z) := fun ζ => by
  rw [map_mul, nval_mul]; exact add_nonneg (hx ζ) (hz ζ)

lemma intAll_neg {x : LamL hs} (hx : IntAllL hs x) : IntAllL hs (-x) := fun ζ => by
  rw [map_neg, nval_neg']; exact hx ζ

def prodSet (x z : LamL hs) : Set (LamL hs) := {u | ∃ l₁ l₂, u = hdList hs l₁ x * hdList hs l₂ z}

lemma hdL_closure (x z : LamL hs) (β : Idx D j G.N →₀ ℕ) {u : LamL hs}
    (hu : u ∈ AddSubmonoid.closure (prodSet hs x z)) : hdL hs β u ∈ AddSubmonoid.closure (prodSet hs x z) := by
  induction hu using AddSubmonoid.closure_induction with
  | mem u hu =>
    obtain ⟨l₁, l₂, rfl⟩ := hu
    rw [hdL_mul]
    exact AddSubmonoid.sum_mem _ fun q _ => AddSubmonoid.subset_closure ⟨q.1 :: l₁, q.2 :: l₂, rfl⟩
  | zero => rw [map_zero]; exact AddSubmonoid.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact AddSubmonoid.add_mem _ ha hb

lemma hdList_mul_mem (x z : LamL hs) (l : List (Idx D j G.N →₀ ℕ)) :
    hdList hs l (x * z) ∈ AddSubmonoid.closure (prodSet hs x z) := by
  induction l with
  | nil => exact AddSubmonoid.subset_closure ⟨[], [], rfl⟩
  | cons β l ih => rw [hdList_cons]; exact hdL_closure hs x z β ih

lemma intAll_of_mem_closure {x z : LamL hs} (hx : ∀ l, IntAllL hs (hdList hs l x)) (hz : ∀ l, IntAllL hs (hdList hs l z))
    {u : LamL hs} (hu : u ∈ AddSubmonoid.closure (prodSet hs x z)) : IntAllL hs u := by
  induction hu using AddSubmonoid.closure_induction with
  | mem u hu =>
    obtain ⟨l₁, l₂, rfl⟩ := hu
    exact intAll_mul hs (hx l₁) (hz l₂)
  | zero => exact intAll_zero hs
  | add u v _ _ hu hv => exact intAll_add hs hu hv

def RGL : Subring (LamL hs) where
  carrier := {r | ∀ l, IntAllL hs (hdList hs l r)}
  zero_mem' := fun l => by rw [hdList_zero]; exact intAll_zero hs
  one_mem' := fun l => by
    rcases hdList_one hs l with h | h
    · rw [h]; exact intAll_zero hs
    · rw [h]; exact intAll_one hs
  add_mem' := fun {a b} ha hb l => by rw [hdList_add]; exact intAll_add hs (ha l) (hb l)
  neg_mem' := fun {a} ha l => by rw [hdList_neg]; exact intAll_neg hs (ha l)
  mul_mem' := fun {a b} ha hb l => intAll_of_mem_closure hs ha hb (hdList_mul_mem hs a b l)

lemma mem_RGL {r : LamL hs} : r ∈ RGL hs ↔ ∀ l, IntAllL hs (hdList hs l r) := Iff.rfl

lemma RGL_hd (β : Idx D j G.N →₀ ℕ) {r : LamL hs} (hr : r ∈ RGL hs) : hdL hs β r ∈ RGL hs := fun l => by
  rw [hdList_append]; exact hr _

lemma RGL_int {r : LamL hs} (hr : r ∈ RGL hs) (ζ : PtsG G la) : 0 ≤ nval (hs ζ).T.V 1 (evL hs ζ r) := hr [] ζ

lemma mem_RGL_of_stable {S : Set (LamL hs)} (hS : ∀ β, ∀ s ∈ S, hdL hs β s ∈ S) (hI : ∀ s ∈ S, IntAllL hs s)
    {r : LamL hs} (hr : r ∈ S) : r ∈ RGL hs := by
  intro l
  have : hdList hs l r ∈ S := by
    induction l with
    | nil => exact hr
    | cons β l ih => rw [hdList_cons]; exact hS β _ ih
  exact hI _ this

def eFormL (F : X.Forms) : LamL hs :=
  ιL hs (algebraMap (Rp (xplus X E hM) la G.N) (Lc (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N F))

lemma eFormL_hd (F : X.Forms) {β : Idx D j G.N →₀ ℕ} (hβ : β ≠ 0) : hdL hs β (eFormL hs F) = 0 := by
  unfold eFormL
  rw [hdL_ι]
  have : hasse (xplus X E hM) la G.w β
      (algebraMap (Rp (xplus X E hM) la G.N) (Lc (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N F)) =
      algebraMap (Rp (xplus X E hM) la G.N) (Lc (xplus X E hM) la G.w)
        (hasseRp (xplus X E hM) la G.N β (emb (xplus X E hM) la G.N F)) :=
    Tay.loc_co (Submonoid.powers (sec (xplus X E hM) la G.w 0)) (Lc (xplus X E hM) la G.w)
      (tayRp (xplus X E hM) la G.N) (tayRp_isTay _ _ _) β _
  have h0 : hasseRp (xplus X E hM) la G.N β (emb (xplus X E hM) la G.N F) = 0 := hasseRp_emb _ _ hβ _
  rw [this, h0, map_zero, map_zero]

lemma evL_eFormL (ζ : PtsG G la) (F : X.Forms) :
    evL hs ζ (eFormL hs F) = (hs ζ).ev (emb (xplus X E hM) la G.N F) := by
  unfold eFormL
  rw [evL_ι, liftC_alg]

lemma eFormL_int {w : WeightFamilies.Wt D j} (F : B.Cusp j w) (hF : ∀ ζ, 0 ≤ E.vAt' la (y ζ) (X.inc w F)) :
    IntAllL hs (eFormL hs (X.inc w F)) := fun ζ => by
  rw [evL_eFormL, ← e_mul_nval (hs ζ).ep_pos]
  have h := hF ζ
  rw [(hs ζ).hv w F] at h
  exact EReal.mul_nonneg (by exact_mod_cast Nat.zero_le _) h

def ιW : Lw (xplus X E hM) la G.w →+* LamL hs := ιL hs

lemma evW_ι (ζ : PtsG G la) (x : Lw (xplus X E hM) la G.w) : evL hs ζ (ιW hs x) = (hs ζ).lift x :=
  evL_ι hs ζ x

lemma hdW_ι (β : Idx D j G.N →₀ ℕ) (x : Lw (xplus X E hM) la G.w) :
    hdL hs β (ιW hs x) = ιW hs (hasse (xplus X E hM) la G.w β x) :=
  hdL_ι hs β x

lemma hdW_mul (β : Idx D j G.N →₀ ℕ) (x z : LamL hs) :
    hdL hs β (x * z) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, hdL hs q.1 x * hdL hs q.2 z :=
  hdL_mul hs β x z

lemma isUnit_of_lift_ne {x : Lw (xplus X E hM) la G.w} (hx : ∀ ζ, (hs ζ).lift x ≠ 0) : IsUnit (ιW hs x) :=
  IsLocalization.map_units (LamL hs) (⟨x, hx⟩ : locSub hs)

lemma evL_eq_zero_of_mem {u : LamL hs}
    (hu : u ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      ιW hs (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))) (ζ : PtsG G la) :
    evL hs ζ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [evW_ι, coe_sfr, (hs ζ).lift_frac, (hs ζ).onS i, zero_mul]
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

lemma toE_eq_top {w : WithTop ℤ} (h : toE w = ⊤) : w = ⊤ := by
  cases w with
  | top => rfl
  | coe n => exact absurd h (EReal.coe_ne_top _)

end Formalism.L2.Pj

namespace Formalism.L2.Pj

open Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem eq_zero_of_ord_top {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {A : Type*} [CommRing A] [Algebra O A] {ϖ : O} [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (c : A)
    (hc : ∀ ζ : Pts O A, ord ϖ ζ c = ⊤) : c = 0 := by
  obtain ⟨n, hn⟩ := h.denom c
  have hb : (⟨ϖ ^ n • c, hn⟩ : ↥(As O A)) = 0 := by
    apply eq_zero_of_localization
    intro J hJ
    let ζ : Pts O A := ⟨J, hJ⟩
    have h1 := hc ζ
    rw [ord_eq ζ h hn, ordAt] at h1
    have h2 : vL ζ ⟨ϖ ^ n • c, hn⟩ = ⊤ := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      rw [← hk, ENat.map_natCast, ← WithTop.coe_add] at h1
      exact WithTop.coe_ne_top h1
    exact (vL_eq_top_iff ζ _).1 h2
  have h3 : ϖ ^ n • c = 0 := congrArg Subtype.val hb
  rw [Algebra.smul_def, map_pow] at h3
  exact (h.isUnit.pow n).mul_right_eq_zero.1 h3

end Formalism.L2.Pj

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la}

lemma curve_span_mem_Jid {g0 : B.Cusp j wF} (CM : CurveModel G la g0) {z : ↥CM.A'}
    (hz : z ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, CM.sA i⟩ : ↥CM.A'))) :
    (z : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact sfr_succ_mem_Jid _ _ _ i
  | zero => exact Ideal.zero_mem _
  | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
  | smul a b _ hb => rw [smul_eq_mul, Subalgebra.coe_mul]; exact Ideal.mul_mem_left _ _ hb

variable (hs : ∀ ζ, SecPt ζ (y ζ))

theorem res_ker_of (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w)) {g0 : B.Cusp j wF} (CM : CurveModel G la g0)
    (hg0 : ∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0)
    (x : ↥(HK (xplus X E hM) la G.w wF))
    (hx : ιW hs (x : Lw (xplus X E hM) la G.w) ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ιW hs (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))) :
    toA0K (xplus X E hM) la G.w wF x = 0 := by
  have hU := isUnif_of_ring (G := G) hfd
  have hD : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_ring hfd hred
  have hz : ∀ ζ, (hs ζ).lift (x : Lw (xplus X E hM) la G.w) = 0 := fun ζ => by
    rw [← evW_ι]; exact evL_eq_zero_of_mem hs hx ζ
  obtain ⟨m, a, ha⟩ := CM.base_form_local x
  have hJh : ((CM.h : ↥(Frac0 (xplus X E hM) la G.w)) - 1) ∈ Jid (xplus X E hM) la G.w := by
    have := curve_span_mem_Jid CM CM.h_one
    rwa [Subalgebra.coe_sub, Subalgebra.coe_one] at this
  have hlh : ∀ ζ, (hs ζ).lift (((CM.h : ↥(Frac0 (xplus X E hM) la G.w))) : Lw (xplus X E hM) la G.w) = 1 :=
    fun ζ => by
      have h1 := (hs ζ).lift_Jid hJh
      rwa [Subalgebra.coe_sub, Subalgebra.coe_one, map_sub, map_one, sub_eq_zero] at h1
  have hla : ∀ ζ, (hs ζ).lift (((a : ↥(Frac0 (xplus X E hM) la G.w))) : Lw (xplus X E hM) la G.w) = 0 :=
    fun ζ => by
      have h1 := congrArg (hs ζ).lift ha
      rw [map_mul, map_mul, map_pow, hlh ζ, hz ζ, one_pow, mul_zero, (hs ζ).lift_alg] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (hg0 ζ)
  have hoa : toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) = 0 := by
    apply eq_zero_of_ord_top hU
    intro ζ
    have h1 := (hs ζ).ord (a : ↥(Frac0 (xplus X E hM) la G.w))
    rw [hla ζ, nval_zero] at h1
    exact toE_eq_top h1
  have haJ : (a : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w :=
    (toOsK_eq_zero_iff _ _ _ _).1 hoa
  have hJm : (CM.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m - 1 ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_pow, map_one]
    have : toOsK (xplus X E hM) la G.w (CM.h : ↥(Frac0 (xplus X E hM) la G.w)) = 1 := by
      rw [← sub_eq_zero, ← map_one (toOsK (xplus X E hM) la G.w), ← map_sub]
      exact (toOsK_eq_zero_iff _ _ _ _).2 hJh
    rw [this, one_pow, sub_self]
  have hg' : algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
      (emb (xplus X E hM) la G.N (X.inc wF g0)) ∈ HK (xplus X E hM) la G.w wF := by
    rw [← frac_zero]
    exact frac_mem_HK _ _ _ (by rw [addL_zero]; exact emb_mem_Vw _ _ _ wF g0)
  let g' : ↥(HK (xplus X E hM) la G.w wF) := ⟨_, hg'⟩
  have e3 : (CM.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x = (a : ↥(Frac0 (xplus X E hM) la G.w)) • g' := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_smul, Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul,
      SubmonoidClass.coe_pow]
    exact ha
  have e1 : toA0K (xplus X E hM) la G.w wF (((CM.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m - 1) • x) = 0 :=
    (reduction_eq_zero_iff_mem_ideal_smul _ _ _ _ _).2 (Submodule.smul_mem_smul hJm Submodule.mem_top)
  have e2 : toA0K (xplus X E hM) la G.w wF ((a : ↥(Frac0 (xplus X E hM) la G.w)) • g') = 0 :=
    (reduction_eq_zero_iff_mem_ideal_smul _ _ _ _ _).2 (Submodule.smul_mem_smul haJ Submodule.mem_top)
  calc toA0K (xplus X E hM) la G.w wF x
      = toA0K (xplus X E hM) la G.w wF ((CM.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x) -
          toA0K (xplus X E hM) la G.w wF (((CM.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m - 1) • x) := by
        rw [← map_sub, sub_smul, one_smul, sub_sub_cancel]
    _ = 0 := by rw [e3, e2, e1, sub_zero]

end Formalism.L2.Pj
