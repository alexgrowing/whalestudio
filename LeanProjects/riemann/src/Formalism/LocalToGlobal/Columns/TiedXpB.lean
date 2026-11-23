import Formalism.LocalToGlobal.Columns.TiedXpU
import Formalism.LocalToGlobal.Columns.TiedFv

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))
  (h : BasePi ST π)

theorem tb_psi_incl {P : Pl E} (hov : IsOver v P) (t : baseDualV hc n ST v) (x : Fin n → E) (r : 𝓞 E)
    (ht : t.1 = fun a => inclE (F := F) (v.adicCompletion F) (x a))
    (hr : algebraMap (𝓞 E) E r = star (algebraMap (𝓞 E) E π) * x (lastIdx n)) :
    rll_psi hc n v h P t = Ideal.Quotient.mk P.asIdeal r := by
  have hm : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : Formalism.BasicNotions.intV E v) : E ⊗[F] v.adicCompletion F) ∈
      Formalism.BasicNotions.intV E v := mul_mem (rll_incl_int v r) (one_mem _)
  have h1 := rll_rho_incl_mul v P r 1 hm
  rw [rll_rho_one v hov, mul_one] at h1
  rw [← h1]
  show rll_rho v P _ = rll_rho v P _
  congr 1
  apply Subtype.ext
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π)) * t.1 (lastIdx n) =
    inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : Formalism.BasicNotions.intV E v) : E ⊗[F] v.adicCompletion F)
  rw [ht, ← map_mul, ← hr]
  exact (mul_one _).symm

end Fun

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

variable (c₀ : DiaG X.E (Pr.vT u))

theorem hermForm_lastVector_apply (x : Fin n → X.E) :
    hform (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E)
      (Pi.single (lastIdx n) (algebraMap (𝓞 X.E) X.E (Pr.piT u))) x =
      star (algebraMap (𝓞 X.E) X.E (Pr.piT u)) * x (lastIdx n) := by
  refine (rf_hform_one (X := X) _ _).trans ?_
  rw [hStd_apply, Finset.sum_eq_single (lastIdx n)]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tb_fvMe_fLoc (P : Pr.vT u) (hc₀ : (c₀ P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)))
    (t : baseDualV hc n (Pr.vT u) (tieEV hc hX hPr u P).1) (x : Fin n → X.E) (r : 𝓞 X.E)
    (ht : t.1 = fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (x a))
    (hr : algebraMap (𝓞 X.E) X.E r = star (algebraMap (𝓞 X.E) X.E (Pr.piT u)) * x (lastIdx n)) :
    fvMe hc hX hPr u c₀ P (fLoc hc n (Pr.vT u) (tieEV hc hX hPr u P).1 t) = Ideal.Quotient.mk P.1.asIdeal r := by
  have h1 : Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (tieInv_spec hPr u P)
  have ha : (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) = 1 := (congrArg (· * _) hc₀).trans h1
  have hp := tb_psi_incl hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) (tieEV_over hc hX hPr u P) t x r ht hr
  refine (fvMeL_fLoc hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.2 (tieEV_over hc hX hPr u P)
    ((basePi_of_ok hX hPr u).over_unique hc P.2 (tieEV_over hc hX hPr u P)) _ _ (fv_unit hPr u c₀ P) t).trans ?_
  exact ((congrArg (· * rll_psi hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.1 t) ha).trans (one_mul _)).trans hp

variable (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

set_option maxHeartbeats 1000000 in

theorem tb_baseFv (P : Pr.vT u) (hc₀ : (c₀ P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)))
    (t : latS (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (intV X.E (tieEV hc hX hPr u P).1)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) Q.J (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb)))
    (x : Fin n → X.E) (r : 𝓞 X.E)
    (ht : t.1 = fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (x a))
    (hr : algebraMap (𝓞 X.E) X.E r =
      hform (hc.sig : X.E →+* X.E) Q.J (Pi.single (lastIdx n) (algebraMap (𝓞 X.E) X.E (Pr.piT u))) x) :
    tieFMe hc hX hPr σ₀ u Λ c₀ s hS hs Q P
      ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fT (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 t) =
        Ideal.Quotient.mk P.1.asIdeal r := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact tb_fvMe_fLoc hc hX hPr u c₀ P hc₀ t x r ht (hr.trans (hermForm_lastVector_apply hc u x))

omit [NeZero n] in

theorem tb_colDia_top (hPr : Pr.Ok) (u : Pr.Word) (R : Ranks) (P : Pr.vT u) :
    (colDia (X := X) (Pr := Pr) R u R.m P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) := by
    have hmax : P.1.asIdeal.IsMaximal := P.1.isMaximal
    let _ := Ideal.Quotient.field P.1.asIdeal
    exact isUnit_iff_ne_zero.2 fun h0 => conj_piT_notMem hPr u P (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  unfold colDia
  rw [if_neg (lt_irrefl _)]
  unfold diaT
  rw [dif_pos hu]
  rfl

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

set_option maxHeartbeats 1000000 in

theorem tilBaseFv (u : d.what₂.Word) :
    CF.TilBaseFv (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) (formModuleEquivAtPlace a hS hH hQ u d.R.m le_rfl) :=
  fun v t x r ht hr =>
    tb_baseFv d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
      (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl) v
      (tb_colDia_top d.hPr u d.R v) t x r ht hr

end Rec

end Formalism.L2.Col
