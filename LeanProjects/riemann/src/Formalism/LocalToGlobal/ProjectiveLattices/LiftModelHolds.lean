import Formalism.LocalToGlobal.ProjectiveLattices.LiftModelPf

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ))

abbrev g0H (g0 : B.Cusp j wF) : ↥(HK (xplus X E hM) la G.w wF) :=
  toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩

abbrev g0L (g0 : B.Cusp j wF) : LamL (hsW hw) :=
  ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)))

theorem inclusion_smul_cusp_eq_mul (g0 : B.Cusp j wF) (b : ↥(Frac0 (xplus X E hM) la G.w)) :
    ιW (hsW hw) ((b • g0H g0 : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
      ιW (hsW hw) (b : Lw (xplus X E hM) la G.w) * g0L hw g0 := by
  rw [CurveModel.coe_smul_base_cusp_form (g0 := g0) b, map_mul]

theorem approx_of' (g0 : B.Cusp j wF) {s : LamL (hsW hw)}
    (hs : s ∈ appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw)) (n : ℕ) {r : LamL (hsW hw)}
    (hr : r ∈ RGW hw) : ∃ x : ↥(HK (xplus X E hM) la G.w wF),
      ιW (hsW hw) (x : Lw (xplus X E hM) la G.w) - r * (s * g0L hw g0) ∈ IW hw ^ n := by
  obtain ⟨f, hf, hfr⟩ := (appSub _ _ _).mul_mem hr.2 hs n
  refine ⟨(⟨f, hf⟩ : ↥(Frac0 (xplus X E hM) la G.w)) • g0H g0, ?_⟩
  rw [inclusion_smul_cusp_eq_mul]
  have e : ιW (hsW hw) f * g0L hw g0 - r * (s * g0L hw g0) = -((r * s - ιW (hsW hw) f) * g0L hw g0) := by ring
  rw [e]
  exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hfr)

theorem iterHd_eq_hdList (l : List (Idx D j G.N →₀ ℕ)) (x : LamL (hsW hw)) :
    iterHd (hdL (hsW hw)) l x = hdList (hsW hw) l x := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, hdList_cons, ih]

theorem mem_RG_of' {g0 : B.Cusp j wF} (C : CurveModel G la g0) (f d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0)
    (hint : ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la), 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ
      (hdList (hsW hw) l (ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * ↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹)))) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * ↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ ∈ RGW hw :=
  ⟨fun l ζ => by
    show 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ (iterHd (hdL (hsW hw)) l _))
    rw [iterHd_eq_hdList]
    exact hint l ζ, (appSub _ _ _).mul_mem (app_of_mem hw f) (inv_app hw C d hd)⟩

theorem ball_of {g0 : B.Cusp j wF} (C : CurveModel G la g0) (FP FQ : ↥(Frac0 (xplus X E hM) la G.w))
    (hval : ∀ ζ, (hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      (hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w)) +
        vV (hsW hw ζ).T.V ((hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
        vV (hsW hw ζ).T.V ((hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w)))
    {v : LamL (hsW hw)} (hv : ιW (hsW hw) (FQ : Lw (xplus X E hM) la G.w) * v = 1)
    (hlift : ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹))))
    (a : SectionSheafQuotient (xplus X E hM) la G.w wF) (ha : a ∈ (secQ y (hsW hw) g0).A0) :
    ∃ r ∈ RGW hw, ∃ x : ↥(HK (xplus X E hM) la G.w wF), toA0K (xplus X E hM) la G.w wF x = a ∧
      ιW (hsW hw) (x : Lw (xplus X E hM) la G.w) - r * ((ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * v) * g0L hw g0) ∈
        IW hw := by
  set e' := (ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * v) * g0L hw g0 with he'
  have hball : a ∈ ball (unifO (xplus X E hM) la G.N) (secQ y (hsW hw) g0).e (secQ y (hsW hw) g0).c := ha
  clear ha
  induction hball using Submodule.span_induction with
  | zero => exact ⟨0, (RGW hw).zero_mem, 0, map_zero _, by simp⟩
  | add a b _ _ iha ihb =>
    obtain ⟨r1, hr1, x1, hx1, h1⟩ := iha
    obtain ⟨r2, hr2, x2, hx2, h2⟩ := ihb
    refine ⟨r1 + r2, (RGW hw).add_mem hr1 hr2, x1 + x2, by rw [map_add, hx1, hx2], ?_⟩
    have e : ιW (hsW hw) ((x1 + x2 : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) - (r1 + r2) * e' =
        (ιW (hsW hw) (x1 : Lw (xplus X E hM) la G.w) - r1 * e') +
          (ιW (hsW hw) (x2 : Lw (xplus X E hM) la G.w) - r2 * e') := by
      rw [Submodule.coe_add, map_add]; ring
    rw [e]; exact Ideal.add_mem _ h1 h2
  | smul b a _ iha =>
    obtain ⟨r, hr, x, hx, hxr⟩ := iha
    obtain ⟨fb, hfb⟩ := toOsK_surjective (xplus X E hM) la G.w (b : OsK (xplus X E hM) la G.w)
    have hint : ∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (fb : Lw (xplus X E hM) la G.w)) := fun ζ => by
      rw [show (hw ζ).toSecPt.lift (fb : Lw (xplus X E hM) la G.w) = _ from (hw ζ).evW fb b hfb]
      exact nval_alg_nonneg _
    obtain ⟨f, d, hd, hfd, hint'⟩ := hlift fb hint
    set u : LamL (hsW hw) := ↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ with hu
    have hdu : ιW (hsW hw) (d : Lw (xplus X E hM) la G.w) * u = 1 := IsUnit.mul_val_inv _
    have hrb : ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * u ∈ RGW hw := mem_RG_of' hw C f d hd hint'
    have hz : fb * d - f ∈ Jid (xplus X E hM) la G.w := by
      rw [← toOsK_eq_zero_iff, map_sub, map_mul, hfd, hfb]; ring
    have hzI := ιW_Jid hw hz
    push_cast at hzI
    refine ⟨ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * u * r, (RGW hw).mul_mem hrb hr, fb • x, ?_, ?_⟩
    · rw [CurveModel.fractionToIntegralSection_smul_eq, hfb, hx]; rfl
    · rw [CurveModel.coe_smul', map_mul]
      have e : ιW (hsW hw) (fb : Lw (xplus X E hM) la G.w) * ιW (hsW hw) (x : Lw (xplus X E hM) la G.w) -
          ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * u * r * e' =
          ιW (hsW hw) (fb : Lw (xplus X E hM) la G.w) * (ιW (hsW hw) (x : Lw (xplus X E hM) la G.w) - r * e') +
            (u * (r * e')) * ιW (hsW hw) ((fb : Lw (xplus X E hM) la G.w) * (d : Lw (xplus X E hM) la G.w) -
              (f : Lw (xplus X E hM) la G.w)) := by
        rw [map_sub, map_mul]
        linear_combination (-(ιW (hsW hw) (fb : Lw (xplus X E hM) la G.w) * r * e')) * hdu
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxr) (Ideal.mul_mem_left _ _ hzI)
  | mem a ha =>
    have hgen : IsGen (OsK (xplus X E hM) la G.w) (secQ y (hsW hw) g0).e := C.isGen
    set c : OsK (xplus X E hM) la G.w := coord (secQ y (hsW hw) g0).e a with hc
    obtain ⟨fc, hfc⟩ := toOsK_surjective (xplus X E hM) la G.w c
    obtain ⟨bp, hbp⟩ := (isUnit_toOsK_of_lift hw C FP (fun ζ => (hval ζ).1)).exists_right_inv
    obtain ⟨vp, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w bp
    have hvp : ∀ ζ, (hsW hw ζ).lift (vp : Lw (xplus X E hM) la G.w) =
        ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w))⁻¹ := by
      intro ζ
      have hz : FP * vp - 1 ∈ Jid (xplus X E hM) la G.w := by
        rw [← toOsK_eq_zero_iff, map_sub, map_one, map_mul, hbp, sub_self]
      have h0 := (hsW hw ζ).lift_Jid hz
      rw [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, map_sub, map_mul, map_one, sub_eq_zero] at h0
      exact eq_inv_of_mul_eq_one_right h0
    set g := fc * FQ * vp with hg
    have hgint : ∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w)) := by
      intro ζ
      obtain ⟨hP0, hQ0, hPQ⟩ := hval ζ
      have h1 : (hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w) =
          (hsW hw ζ).lift (fc : Lw (xplus X E hM) la G.w) *
            ((hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w) * ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w))⁻¹) := by
        rw [hg, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, map_mul, hvp ζ, mul_assoc]
      have hne : (hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w) *
          ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w))⁻¹ ≠ 0 := mul_ne_zero hQ0 (inv_ne_zero hP0)
      have hvq : vV (hsW hw ζ).T.V ((hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w) *
          ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w))⁻¹) =
          vV (hsW hw ζ).T.V ((hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) := by
        rw [vV_mul hQ0 (inv_ne_zero hP0), vV_inv' hP0]; omega
      have hord := (hsW hw ζ).ord fc
      rw [hfc] at hord
      have hm := ha ζ
      simp only [ordV] at hm
      have h2 := toE_nonneg' hm
      rw [toE_add_coe] at h2
      have h3 : ((secQ y (hsW hw) g0).c ζ : ℤ) = vV (hsW hw ζ).T.V ((hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) := rfl
      rw [h3] at h2
      change 0 ≤ nval (hsW hw ζ).T.V 1 ((hsW hw ζ).lift (g : Lw (xplus X E hM) la G.w))
      rw [h1, nval_mul, nval_of_ne hne, hvq, ← hord]
      simpa using h2
    obtain ⟨f, d, hd, hfd, hint'⟩ := hlift g hgint
    set u : LamL (hsW hw) := ↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ with hu
    have hdu : ιW (hsW hw) (d : Lw (xplus X E hM) la G.w) * u = 1 := IsUnit.mul_val_inv _
    have hz : fc * d * FQ - f * FP ∈ Jid (xplus X E hM) la G.w := by
      rw [← toOsK_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, hfd, hg, map_mul, map_mul, hfc]
      linear_combination (-(c * toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w FQ)) * hbp
    have hzI := ιW_Jid hw hz
    push_cast at hzI
    refine ⟨ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * u, mem_RG_of' hw C f d hd hint', fc • g0H g0, ?_, ?_⟩
    · rw [CurveModel.fractionToIntegralSection_smul_eq, hfc]
      exact coord_smul_self hgen a
    · rw [inclusion_smul_cusp_eq_mul, he']
      have e : ιW (hsW hw) (fc : Lw (xplus X E hM) la G.w) * g0L hw g0 -
          ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) * u * (ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * v * g0L hw g0) =
          (g0L hw g0 * u * v) * ιW (hsW hw) ((fc : Lw (xplus X E hM) la G.w) * (d : Lw (xplus X E hM) la G.w) *
            (FQ : Lw (xplus X E hM) la G.w) - (f : Lw (xplus X E hM) la G.w) * (FP : Lw (xplus X E hM) la G.w)) := by
        rw [map_sub, map_mul, map_mul, map_mul]
        linear_combination (-(g0L hw g0 * ιW (hsW hw) (fc : Lw (xplus X E hM) la G.w))) * hdu +
          (-(g0L hw g0 * ιW (hsW hw) (fc : Lw (xplus X E hM) la G.w) * ιW (hsW hw) (d : Lw (xplus X E hM) la G.w) * u)) * hv
      rw [e]
      exact Ideal.mul_mem_left _ _ hzI

set_option maxHeartbeats 1600000 in

theorem liftModelSt_of (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (hL : LocRingSt G la) :
    LiftModelSt G la := by
  intro y hw g0 T hCM hg0
  obtain ⟨C⟩ := hCM
  obtain ⟨⟨k, p, q, hp, hq, hpc, hqc, hpq⟩, hlift⟩ := hL y hw g0 ⟨C⟩ hg0
  have hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
    exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv
  have hred : IsReduced (OsK (xplus X E hM) la G.w) := by
    have : IsReduced (↥C.A' ⧸ C.JA) := C.red
    exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective
  have hQl : ∀ ζ, (hsW hw ζ).lift (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) q) ≠ 0 :=
    fun ζ => by rw [SecPt.lift_alg]; exact (hpq ζ).2.1
  let FP : ↥(Frac0 (xplus X E hM) la G.w) :=
    ⟨frac (xplus X E hM) la G.w k p, (mem_Frac0 _ _ _).2 (frac_mem_Hfr _ _ _ hp)⟩
  let FQ : ↥(Frac0 (xplus X E hM) la G.w) :=
    ⟨frac (xplus X E hM) la G.w k q, (mem_Frac0 _ _ _).2 (frac_mem_Hfr _ _ _ hq)⟩
  have hw0 : ∀ ζ, ((hsW hw ζ).ev (sec (xplus X E hM) la G.w 0))⁻¹ ^ k ≠ 0 :=
    fun ζ => pow_ne_zero _ (inv_ne_zero (hsW hw ζ).s0.ne_zero)
  have hFP0 : ∀ ζ, (hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w) ≠ 0 := fun ζ => by
    show (hsW hw ζ).lift (frac (xplus X E hM) la G.w k p) ≠ 0
    rw [SecPt.lift_frac]; exact mul_ne_zero (hpq ζ).1 (hw0 ζ)
  have hFQ0 : ∀ ζ, (hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w) ≠ 0 := fun ζ => by
    show (hsW hw ζ).lift (frac (xplus X E hM) la G.w k q) ≠ 0
    rw [SecPt.lift_frac]; exact mul_ne_zero (hpq ζ).2.1 (hw0 ζ)
  have hvalF : ∀ ζ, vV (hsW hw ζ).T.V ((hsW hw ζ).lift (FP : Lw (xplus X E hM) la G.w)) +
      vV (hsW hw ζ).T.V ((hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (FQ : Lw (xplus X E hM) la G.w)) := fun ζ => by
    show vV (hsW hw ζ).T.V ((hsW hw ζ).lift (frac (xplus X E hM) la G.w k p)) + _ =
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (frac (xplus X E hM) la G.w k q))
    rw [SecPt.lift_frac, SecPt.lift_frac, vV_mul (hpq ζ).1 (hw0 ζ), vV_mul (hpq ζ).2.1 (hw0 ζ)]
    have h := (hpq ζ).2.2
    dsimp only [hsW] at h ⊢
    omega
  have uQ := isUnit_of_lift_ne (hsW hw) hQl
  have uFQ := isUnit_of_lift_ne (hsW hw) hFQ0
  have hv : ιW (hsW hw) (FQ : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹ = 1 := uFQ.mul_val_inv
  have key : ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) p) *
      ιW (hsW hw) (FQ : Lw (xplus X E hM) la G.w) = ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) *
      ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) q) := by
    rw [← map_mul, ← map_mul]
    congr 1
    show _ * frac (xplus X E hM) la G.w k q = frac (xplus X E hM) la G.w k p * _
    rw [frac_apply, frac_apply]; ring
  have hs_eq : ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹ =
      ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) p) * ↑uQ.unit⁻¹ := by
    calc ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹
        = ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹ *
            (ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) q) * ↑uQ.unit⁻¹) := by
          rw [uQ.mul_val_inv, mul_one]
      _ = (ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) *
            ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) q)) * ↑uFQ.unit⁻¹ *
            ↑uQ.unit⁻¹ := by ring
      _ = (ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) p) *
            ιW (hsW hw) (FQ : Lw (xplus X E hM) la G.w)) * ↑uFQ.unit⁻¹ * ↑uQ.unit⁻¹ := by rw [key]
      _ = ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) p) * ↑uQ.unit⁻¹ *
            (ιW (hsW hw) (FQ : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹) := by ring
      _ = _ := by rw [hv, mul_one]
  have hsApp : ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹ ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) :=
    (appSub _ _ _).mul_mem (app_of_mem hw FP) (inv_app hw C FQ hFQ0)
  have hconst : ∀ r : Rp (xplus X E hM) la G.N, (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β r = 0) →
      ∀ β, β ≠ 0 → hdL (hsW hw) β (ιW (hsW hw) (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) r)) = 0 := by
    intro r hr β hβ
    rw [hdW_ι, show hasse (xplus X E hM) la G.w β (algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) r) =
      algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (hasseRp (xplus X E hM) la G.N β r) from
        hasse_algebraMap _ _ _ β r, hr β hβ, map_zero, map_zero]
  refine ⟨{
    Λ := LamL (hsW hw)
    ι := ιW (hsW hw)
    hd := hdL (hsW hw)
    hd_zero := hdL_zero (hsW hw)
    hd_ι := hdW_ι (hsW hw)
    hd_mul := hdW_mul (hsW hw)
    ev := evL (hsW hw)
    ev_ι := evW_ι (hsW hw)
    RG := RGW hw
    RG_hd := RGW_hd hw
    RG_int := fun ζ r hr => RGW_int hw ζ r hr
    e' := (ιW (hsW hw) (FP : Lw (xplus X E hM) la G.w) * ↑uFQ.unit⁻¹) * g0L hw g0
    e'_hd := fun β hβ => by
      rw [hs_eq]
      exact hd_mul_const (hdW_mul _) (hd_mul_const (hdW_mul _) (hconst p hpc)
        (hd_inv_const (hdL_zero _) (hdW_mul _) uQ (hconst q hqc))) (hconst _ fun β hβ => hasseRp_emb _ _ hβ _) β hβ
    e'_int := fun ζ => by
      rw [hs_eq, map_mul, map_mul, evL_inv, evW_ι, evW_ι, evW_ι, SecPt.lift_alg, SecPt.lift_alg, SecPt.lift_alg]
      obtain ⟨h1, h2, h3⟩ := hpq ζ
      have hne : (hsW hw ζ).ev p * ((hsW hw ζ).ev q)⁻¹ * (hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero h1 (inv_ne_zero h2)) (hg0 ζ)
      rw [nval_of_ne hne, vV_mul (mul_ne_zero h1 (inv_ne_zero h2)) (hg0 ζ), vV_mul h1 (inv_ne_zero h2), vV_inv' h2]
      have h4 : vV (hsW hw ζ).T.V ((hsW hw ζ).ev p) + -vV (hsW hw ζ).T.V ((hsW hw ζ).ev q) +
          vV (hsW hw ζ).T.V ((hsW hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) = 0 := by
        dsimp only [hsW] at h3 ⊢; omega
      rw [h4]; simp
    res_ker := res_ker_of (hsW hw) hfd hred C hg0
    ball := fun a ha => ball_of hw C FP FQ (fun ζ => ⟨hFP0 ζ, hFQ0 ζ, hvalF ζ⟩) hv hlift a ha
    approx := fun r hr => approx_of' hw g0 hsApp (a0 D j T) hr }⟩

end Formalism.L2.Pj
