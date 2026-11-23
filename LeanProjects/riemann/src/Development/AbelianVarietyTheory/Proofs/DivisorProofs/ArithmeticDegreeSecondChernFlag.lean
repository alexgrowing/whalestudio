import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqOfExactRealFormCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBottChernShortExactStatement
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCh2Ring

open MvPolynomial

theorem psum_two (r : ℕ) : psum (Fin r) ℚ 2 = esymm (Fin r) ℚ 1 ^ 2 - 2 * esymm (Fin r) ℚ 2 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin r) ℚ 2 (by norm_num)]
  have e : ({a ∈ Finset.HasAntidiagonal.antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} : Finset (ℕ × ℕ)) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Set.mem_Ioo, Finset.mem_singleton, Prod.mk.injEq]
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · rintro ⟨h1, h2, h3⟩; simp at h1; omega
    · rintro ⟨rfl, rfl⟩; norm_num
  rw [e, Finset.sum_singleton, MvPolynomial.psum_one, ← esymm_one]
  push_cast
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {B : CxForm.BottChern}
  {h : IsRegVar p D}

theorem char_chPart_two (R : CxForm.ArRing B h) {r : ℕ} (E : HermVB p r) :
    R.char E (CxForm.chPart r 2) = (1 / 2 : ℚ) • (R.cl E 1 ^ 2 - 2 * R.cl E 2) := by
  have e : CxForm.chPart r 2 = (1 / 2 : ℚ) •
      ((⟨esymm (Fin r) ℚ 1, esymm_isSymmetric _ _ 1⟩ : symmetricSubalgebra (Fin r) ℚ) ^ 2 -
        2 * ⟨esymm (Fin r) ℚ 2, esymm_isSymmetric _ _ 2⟩) := by
    apply Subtype.ext
    simp only [CxForm.chPart, psum_two]
    norm_num
    left; rfl
  rw [e, map_smul, map_sub, map_mul, map_pow, map_ofNat, R.char_esymm, R.char_esymm]

end GlobalTheory.FlagCh2Ring

namespace GlobalTheory.FlagCh2Ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem bcInt_eq : ∀ (B : CxForm.BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X]
    (h : IsRegVar p 1) (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s))
    (G : g.IsCInf) (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (θ : h.Fld),
    h.IsArForm 1 θ → (∀ σ, (h.atlas σ).IsExact (θ σ - B.bc (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ))) →
    g.BcFinite hS h₁ h₃ → h.integral θ = - g.bcInt hS h₁ h₃ := by
  intro B k _ X p _ h S hS r s g G hi h₁ h₃ θ hθ hex hb
  rw [IsRegVar.integral, VMetric.bcInt, ← finsum_neg_distrib]
  exact finsum_congr fun σ => (GlobalTheory.T.integral_eq_of_exact_real_form_curve k X p h σ _ _ (hθ.1 σ) (hex σ)).trans
    (GlobalTheory.T.integral_bott_chern_short_exact B k X p h S hS r s g G hi h₁ h₃ σ (hb σ))

theorem hermVB_congr {F : X.Modules} {r : ℕ} {m₁ m₂ : VMetric p F r} (e : m₁ = m₂) (H₁ : m₁.IsCInf)
    (H₂ : m₂.IsCInf) : (⟨F, m₁, H₁⟩ : HermVB p r) = ⟨F, m₂, H₂⟩ := by
  subst e; rfl

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r}

def stepVB (H : h.IsCInf) (fl : Vert.Flag E r) (j : Fin (r + 1)) : HermVB p j :=
  ⟨fl.F j, h.restrict (fl.isSubbundle j) (fl.isVB j), H.restrict _ _⟩

theorem restrict_stepMet (fl : Vert.Flag E r) (i : Fin r) (hf : VB.IsSubbundle (fl.step i)) :
    (h.stepMet fl i).restrict hf (fl.isVB i.castSucc) = h.restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc) := by
  refine VMetric.ext (funext fun σ => Met.ext_form fun V s t y hy => ?_)
  have key : ∀ t : Γ(fl.F i.castSucc, V), (fl.ι i.succ).app V ((fl.step i).app V t) = (fl.ι i.castSucc).app V t :=
    fun t => by rw [← fl.step_ι i]; rfl
  refine (((h.stepMet fl i).met σ).form_restrict hf (fl.isVB i.castSucc) s t hy).trans ?_
  refine (((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy)).trans ?_
  rw [key, key]
  exact ((h.met σ).form_restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc) s t hy).symm

theorem isometric_det_step (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) :
    ((VMetric.det (H.restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc))).tens (VMetric.grLB fl i H)).Isometric
      (VMetric.det (H.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ))) := by
  have hf : VB.IsSubbundle (fl.step i) := ⟨inferInstance, 1, fl.isVB_gr i⟩
  have e := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl i) i 1 (h.stepMet fl i)
    (H.restrict _ _) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) hf
  refine (HermLB.Isometric.tens_right ?_ _).trans e
  refine HermLB.isometric_of_chart (fun c => c) (fun _ => le_rfl) (fun x c c' _ _ => rfl) fun σ c y hy => ?_
  change -Real.log ((((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc)).G c y).det.re =
    -Real.log (((h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc)).G c y).det.re
  rw [show ((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc) =
    (h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc) from
      congrArg (fun m : VMetric p _ _ => m.met σ) (restrict_stepMet fl i hf)]

end GlobalTheory.FlagCh2Ring

namespace GlobalTheory.FlagCh2Ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] {B : CxForm.BottChern}
  {hX : IsRegVar p 1} (R : CxForm.ArRing B hX) {E : X.Modules} {r : ℕ} {h : VMetric p E r}

def twiceCh (H : h.IsCInf) (fl : Vert.Flag E r) (j : Fin (r + 1)) : R.CH :=
  R.cl (stepVB H fl j) 1 ^ 2 - 2 * R.cl (stepVB H fl j) 2

theorem deg_twiceCh_succ (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) {x : ℝ}
    (hx : (VMetric.grLB fl i H).IsSelfInter x)
    (hb : (h.stepMet fl i).BcFinite (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) :
    R.deg (twiceCh R H fl i.succ) = R.deg (twiceCh R H fl i.castSucc) + x -
      (h.stepMet fl i).bcInt (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) := by
  have hf : VB.IsSubbundle (fl.step i) := ⟨inferInstance, 1, fl.isVB_gr i⟩
  have H₂ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₁ : ((h.stepMet fl i).restrict hf (fl.isVB i.castSucc)).IsCInf := H₂.restrict _ _
  obtain ⟨θ, hθ, hex, hw⟩ := R.whitney (VMetric.stepSeq_shortExact fl i) H₁ H₂ (H.grMet fl i)
  have hint := bcInt_eq B k X p hX (VMetric.stepSeq fl i) (VMetric.stepSeq_shortExact fl i) i 1 (h.stepMet fl i) H₂ hf
    (fl.isVB i.castSucc) (fl.isVB_gr i) θ hθ hex hb
  have e₁ : (⟨_, (h.stepMet fl i).restrict hf (fl.isVB i.castSucc), H₁⟩ : HermVB p i) = stepVB H fl i.castSucc :=
    hermVB_congr (restrict_stepMet fl i hf) _ _
  have e₂ : (⟨_, h.stepMet fl i, H₂⟩ : HermVB p (i + 1)) = stepVB H fl i.succ := rfl
  rw [e₁, e₂, R.cl_eq_zero (⟨_, h.grMet fl i, H.grMet fl i⟩ : HermVB p 1) 2 (by norm_num)] at hw
  have hl : R.cl (⟨_, h.grMet fl i, H.grMet fl i⟩ : HermVB p 1) 1 = R.c1 (VMetric.grLB fl i H) := R.cl_one _
  rw [hl] at hw
  have hc : R.cl (stepVB H fl i.succ) 1 = R.cl (stepVB H fl i.castSucc) 1 + R.c1 (VMetric.grLB fl i H) := by
    rw [R.cl_one, R.cl_one, ← R.firstChernTensor]
    exact (R.firstChernCongr _ _ (isometric_det_step H fl i)).symm
  have e₃ : twiceCh R H fl i.succ = twiceCh R H fl i.castSucc + R.c1 (VMetric.grLB fl i H) ^ 2 + (R.a θ + R.a θ) := by
    simp only [twiceCh]
    rw [hc]
    linear_combination 2 * hw
  have hsq : R.deg (R.c1 (VMetric.grLB fl i H) ^ 2) = x := R.degreeFirstChernPow _ _ hx
  rw [e₃, map_add, map_add, map_add, hsq, R.deg_a θ hθ, hint]
  ring

end GlobalTheory.FlagCh2Ring

namespace GlobalTheory.FlagCh2Ring

theorem deg_ch2_eq_flag : ∀ (B : CxForm.BottChern) (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S]
    (h : IsRegVar p 1) (R : CxForm.ArRing B h) (r : ℕ) (E : HermVB p r) (fl : Vert.Flag E.E r) (a : ℝ),
    VMetric.IsFlagCh2 E.cInf fl a → R.deg (R.char E (CxForm.chPart r 2)) = a := by
  intro B k _ S p _ h R r E fl a ha
  obtain ⟨hfin, x, hx, rfl⟩ := ha
  have hE (j : ℕ) : R.cl E j = R.cl (stepVB E.cInf fl (Fin.last r)) j :=
    (R.cl_congr (stepVB E.cInf fl (Fin.last r)) E (@asIso _ _ _ _ (fl.ι (Fin.last r)) fl.isIso_last)
      (fun σ V s t y hy => ((E.h.met σ).form_restrict (fl.isSubbundle _) (fl.isVB _) s t hy).symm) j).symm
  let t : Fin (r + 1) → ℝ := fun j => R.deg (twiceCh R E.cInf fl j)
  have h₀ : t 0 = 0 := by
    simp only [t, twiceCh]
    rw [R.cl_eq_zero _ 1 (by simp), R.cl_eq_zero _ 2 (by simp)]
    simp
  have hstep (i : Fin r) : t i.succ - t i.castSucc = x i -
      (E.h.stepMet fl i).bcInt (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) := by
    simp only [t]
    rw [deg_twiceCh_succ R E.cInf fl i (hx i) (hfin i)]
    ring
  have e := (Fin.sum_univ_succ t).symm.trans (Fin.sum_univ_castSucc t)
  have hlast : t (Fin.last r) = ∑ i, (x i -
      (E.h.stepMet fl i).bcInt (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) := by
    rw [← Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_sub_distrib]
    linarith
  rw [char_chPart_two, map_smul, hE 1, hE 2]
  change (1 / 2 : ℚ) • t (Fin.last r) = _
  rw [hlast, Rat.smul_def, Finset.sum_sub_distrib, VMetric.flagBc, Finset.sum_div]
  push_cast
  rw [← Finset.sum_div, ← Finset.sum_div]
  ring

end GlobalTheory.FlagCh2Ring
