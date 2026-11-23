import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

structure SecPt (ζ : PtsG G la) (y : E.Pt' la) where

  T : CDVR

  ep_pos : 0 < ep (unifO (xplus X E hM) la G.N) ζ

  ev : Rp (xplus X E hM) la G.N →+* T.Fr

  hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
    nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F)))

  onS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec (xplus X E hM) la G.w i.succ) = 0

  s0 : IsUnit (ev (sec (xplus X E hM) la G.w 0))

  ord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
    toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
      nval T.V 1 (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) s0 (x : Lw (xplus X E hM) la G.w))

structure FromW (ζ : PtsG G la) (y : E.Pt' la) extends SecPt ζ y where

  ι : Loc ζ →+* T.V

  loc : IsLocalHom ι
  unr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)

  evW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w)) (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
    toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
    IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) toSecPt.s0 (x : Lw (xplus X E hM) la G.w) =
      algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a))

def SecPtSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ ζ : PtsG G la, ∃ y : E.Pt' la, Nonempty (SecPt ζ y)

def secQ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) : LocalPointData G la where
  y ζ := .inr (y ζ)
  g0 := g0
  c ζ := vV (hs ζ).T.V ((hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)))

def InTieSecSt : Prop :=
  ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)
    (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    (∀ ζ, (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (sec (xplus X E hM) la G.w 0))) →
    (j < D.R.m → ∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) →
    (secQ y hs g0).InTie S

section Nval

variable {T : CDVR}

lemma vV_one' : vV T.V (1 : T.Fr) = 0 := by simp [vV]

lemma vV_inv' {b : T.Fr} (hb : b ≠ 0) : vV T.V b⁻¹ = - vV T.V b := by
  have h := vV_mul (V := T.V) hb (inv_ne_zero hb)
  rw [mul_inv_cancel₀ hb, vV_one'] at h
  omega

lemma vV_pow' {b : T.Fr} (hb : b ≠ 0) (k : ℕ) : vV T.V (b ^ k) = k * vV T.V b := by
  induction k with
  | zero => simp [vV_one']
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hb) hb, ih]; push_cast; ring

lemma nval_frac {e : ℕ} (he : 0 < e) (a b : T.Fr) (hb : b ≠ 0) (k : ℕ) :
    nval T.V 1 (a * (b⁻¹) ^ k) = (e : EReal) * (nval T.V e a - (k : EReal) * nval T.V e b) := by
  rw [nval_of_ne hb]
  by_cases ha : a = 0
  · subst ha
    rw [zero_mul, nval_zero, nval_zero]
    have hk : (k : EReal) * (((vV T.V b : ℝ) / e : ℝ) : EReal) = ((k * ((vV T.V b : ℝ) / e) : ℝ) : EReal) := by
      norm_cast
    rw [hk, EReal.top_sub_coe, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · have hab : a * (b⁻¹) ^ k ≠ 0 := mul_ne_zero ha (pow_ne_zero k (inv_ne_zero hb))
    rw [nval_of_ne hab, nval_of_ne ha, vV_mul ha (pow_ne_zero k (inv_ne_zero hb)), vV_pow' (inv_ne_zero hb),
      vV_inv' hb]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (((vV T.V a : ℤ) + (k : ℤ) * -vV T.V b : ℤ) : ℝ) / ((1 : ℕ) : ℝ) =
        (e : ℝ) * ((vV T.V a : ℝ) / e - k * ((vV T.V b : ℝ) / e)) := by
      push_cast; field_simp; ring
    rw [this]
    norm_cast

lemma e_mul_nval {e : ℕ} (he : 0 < e) (x : T.Fr) : (e : EReal) * nval T.V e x = nval T.V 1 x := by
  by_cases hx : x = 0
  · subst hx; rw [nval_zero, nval_zero, EReal.mul_top_of_pos (by exact_mod_cast he)]
  · rw [nval_of_ne hx, nval_of_ne hx]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have : (e : ℝ) * ((vV T.V x : ℝ) / e) = (vV T.V x : ℝ) / ((1 : ℕ) : ℝ) := by
      rw [Nat.cast_one, div_one]; field_simp
    rw [← this]; norm_cast

end Nval

lemma normalized_valuation_mul {T : CDVR} {e : ℕ} (he : 0 < e) (b : T.Fr) (hb : b ≠ 0) :
    (e : ℝ) * (nval T.V e b).toReal = (vV T.V b : ℝ) := by
  rw [nval_of_ne hb, EReal.toReal_coe]
  have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp

lemma toE_add_coe (a : WithTop ℤ) (n : ℤ) : toE (a + (n : WithTop ℤ)) = toE a + ((n : ℝ) : EReal) := by
  cases a with
  | top => simp [toE]
  | coe m =>
    show toE ((m + n : ℤ) : WithTop ℤ) = toE (m : WithTop ℤ) + ((n : ℝ) : EReal)
    simp only [toE]; push_cast; rfl

section Lift

variable {ζ : PtsG G la} {y₀ : E.Pt' la} (h : SecPt ζ y₀)

abbrev SecPt.lift : Lw (xplus X E hM) la G.w →+* h.T.Fr :=
  IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) h.s0

lemma SecPt.lift_alg (r : Rp (xplus X E hM) la G.N) : h.lift (algebraMap _ _ r) = h.ev r :=
  IsLocalization.lift_eq _ r

lemma SecPt.lift_w0inv : h.lift (w0inv (xplus X E hM) la G.w) = (h.ev (sec (xplus X E hM) la G.w 0))⁻¹ := by
  have := congrArg h.lift (section_mul_inverse_eq_one (xplus X E hM) la G.w)
  rw [map_mul, h.lift_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma SecPt.lift_frac (k : ℕ) (g : Rp (xplus X E hM) la G.N) :
    h.lift (frac (xplus X E hM) la G.w k g) = h.ev g * (h.ev (sec (xplus X E hM) la G.w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, h.lift_alg, h.lift_w0inv]

lemma SecPt.lift_Jid {r : ↥(Frac0 (xplus X E hM) la G.w)} (hr : r ∈ Jid (xplus X E hM) la G.w) :
    h.lift (r : Lw (xplus X E hM) la G.w) = 0 := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [coe_sfr, h.lift_frac, h.onS i, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, hx, mul_zero]

lemma SecPt.lift_JHK {u : WeightFamilies.Wt D j} {z : ↥(HK (xplus X E hM) la G.w u)}
    (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w u))) :
    h.lift (z : Lw (xplus X E hM) la G.w) = 0 := by
  refine Submodule.smul_induction_on
    (p := fun z : ↥(HK (xplus X E hM) la G.w u) => h.lift (z : Lw (xplus X E hM) la G.w) = 0) hz ?_ ?_
  · intro r hr m _
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul]
    have : h.lift (algebraMap ↥(Frac0 (xplus X E hM) la G.w) (Lw (xplus X E hM) la G.w) r) = 0 := h.lift_Jid hr
    rw [this, zero_mul]
  · intro x y hx hy
    rw [Submodule.coe_add, map_add, hx, hy, add_zero]

end Lift

theorem inTieSec : InTieSecSt := by
  intro D B P j X E hM ka wL wF G la S y hs g0 hdep het hg0 hgen ζ
  have hd := hdep ζ
  have hg0' := hg0 ζ
  have het' : j < D.R.m → (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc _ G.et)) ≠ 0 := fun hj => het hj ζ
  set h := hs ζ with hh
  have hb : h.ev (sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos
  have hvat : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc w F) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (emb (xplus X E hM) la G.N (X.inc w F))) :=
    fun w F => h.hv w F
  have hQy : (secQ y hs g0).y ζ = .inr (y ζ) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_top _
  · rw [hQy, hd, nval_of_ne hb]; exact EReal.coe_ne_bot _
  · intro hj
    rw [hQy, hvat, nval_of_ne (het' hj)]; exact EReal.coe_ne_top _
  · refine ⟨vV h.T.V (h.ev (sec (xplus X E hM) la G.w 0)), ?_⟩
    simp only [LocalPointData.nu, hQy, hd]
    exact normalized_valuation_mul he _ (hs ζ).s0.ne_zero
  · change (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
      (ep (unifO (xplus X E hM) la G.N) ζ : EReal) * (xplus X E hM).vAt la (.inr (y ζ)) ((xplus X E hM).inc wF g0)
    rw [hvat, e_mul_nval he, nval_of_ne hg0']
    simp
  · intro k g
    rw [h.ord, coe_weightZeroFraction, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl
  · intro k g
    have hgen' : IsGen (OsK (xplus X E hM) la G.w) ((secQ y hs g0).e) := hgen
    set a := toA0K (xplus X E hM) la G.w wF (toHK (xplus X E hM) la G.w wF k
      ⟨emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g), emb_mem_Vw (xplus X E hM) la G.N _ g⟩) with ha
    obtain ⟨x, hx⟩ := toOsK_surjective (xplus X E hM) la G.w (coord ((secQ y hs g0).e) a)
    have hca : coord ((secQ y hs g0).e) a • (secQ y hs g0).e = a := coord_smul_self hgen' a
    have h1 : toA0K (xplus X E hM) la G.w wF (x • toHK0 (xplus X E hM) la G.w wF
        ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) = a := by
      rw [map_smul, ← restriction_apply_eq_reduction, ← hca, ← hx]
      exact (algebraMap_smul (OsK (xplus X E hM) la G.w) x _).symm
    have h2 := (Submodule.Quotient.eq _).1 h1
    have h3 := h.lift_JHK h2
    rw [Submodule.coe_sub, map_sub, sub_eq_zero, Submodule.coe_smul, Algebra.smul_def, map_mul, coe_toHK0,
      coe_toHK, h.lift_alg] at h3
    have h3' : h.lift (x : Lw (xplus X E hM) la G.w) * h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)) =
        h.lift (frac (xplus X E hM) la G.w k (emb (xplus X E hM) la G.N ((xplus X E hM).inc _ g))) := h3
    have hord := h.ord x
    rw [hx] at hord
    simp only [LocalPointData.ordA, ordV]
    rw [toE_add_coe, hord]
    change nval h.T.V 1 (h.lift (x : Lw (xplus X E hM) la G.w)) +
      (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) = _
    have hm := nval_mul (V := h.T.V) 1 (h.lift (x : Lw (xplus X E hM) la G.w))
      (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0)))
    rw [h3', nval_of_ne hg0'] at hm
    have hc : (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℤ) : ℝ) : EReal) =
        (((vV h.T.V (h.ev (emb (xplus X E hM) la G.N (X.inc wF g0))) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) : EReal) := by simp
    rw [hc, ← hm, h.lift_frac, nval_frac he _ _ hb, hQy, hvat, hd]
    rfl

end Formalism.L2.Pj
