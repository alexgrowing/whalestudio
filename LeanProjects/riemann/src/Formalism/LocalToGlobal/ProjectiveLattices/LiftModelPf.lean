import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
import Formalism.LocalToGlobal.ProjectiveLattices.LiftRG
import Formalism.LocalToGlobal.ProjectiveLattices.LiftUnit
import Formalism.LocalToGlobal.ProjectiveLattices.LiftInSt
import Formalism.LocalToGlobal.ProjectiveLattices.LiftModelSt

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

lemma nval_alg_nonneg {T : CDVR} (x : T.V) : 0 ≤ nval T.V 1 (algebraMap T.V T.Fr x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero, nval_zero]; exact le_top
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 hx)
    have h0 : algebraMap T.V T.Fr x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hx
    rw [nval_of_ne h0, vV_alg_of_addVal hk.symm]
    exact EReal.coe_nonneg.2 (by positivity)

lemma nval_inv_nonneg {T : CDVR} {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) : 0 ≤ nval T.V 1 x⁻¹ := by
  rw [nval_of_ne (inv_ne_zero hx), vV_inv' hx, h0]; simp

lemma toE_nonneg' {w : WithTop ℤ} (h : 0 ≤ w) : 0 ≤ toE w := by
  cases w with
  | top => simp [toE]
  | coe n =>
    simp only [toE]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    exact_mod_cast this

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ))

abbrev hsW : ∀ ζ, SecPt ζ (y ζ) := fun ζ => (hw ζ).toSecPt

def IW : Ideal (LamL (hsW hw)) := Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
  ιW (hsW hw) (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

def RGW : Subring (LamL (hsW hw)) :=
  stabSub (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (intSub (fun ζ => (hsW hw ζ).T) (evL (hsW hw))) ⊓
    appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw)

theorem ιW_Jid {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    ιW (hsW hw) (z : Lw (xplus X E hM) la G.w) ∈ IW hw := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Ideal.subset_span ⟨i, rfl⟩
  | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact Ideal.zero_mem _
  | add x z _ _ hx hz => rw [Subalgebra.coe_add, map_add]; exact Ideal.add_mem _ hx hz
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx

theorem RGW_hd (β : Idx D j G.N →₀ ℕ) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) : hdL (hsW hw) β r ∈ RGW hw :=
  ⟨stabSub_hd _ _ _ β hr.1, appSub_hd (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (ιW (hsW hw)) _ _
    (fun β x => hasse (xplus X E hM) la G.w β x) (hdW_ι (hsW hw))
    (fun β f hf => (mem_Frac0 _ _ _).2 (hasse_mem_Hfr _ _ _ ((mem_Frac0 _ _ _).1 hf) β)) β hr.2⟩

theorem RGW_int (ζ : PtsG G la) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) :
    0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ r) :=
  stabSub_le _ _ _ hr.1 ζ

theorem iterHd_ιW (l : List (Idx D j G.N →₀ ℕ)) (x : Lw (xplus X E hM) la G.w) :
    iterHd (hdL (hsW hw)) l (ιW (hsW hw) x) =
      ιW (hsW hw) (l.foldr (fun β z => hasse (xplus X E hM) la G.w β z) x) := by
  induction l with
  | nil => rfl
  | cons β l ih => rw [iterHd_cons, ih, hdW_ι]; rfl

theorem stab_of_hdInt {x : Lw (xplus X E hM) la G.w} (hx : HdIntAt (hsW hw) x) :
    ιW (hsW hw) x ∈ stabSub (hdL_zero (hsW hw)) (hdW_mul (hsW hw))
      (intSub (fun ζ => (hsW hw ζ).T) (evL (hsW hw))) := fun l ζ => by
  show 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ (iterHd (hdL (hsW hw)) l (ιW (hsW hw) x)))
  rw [iterHd_ιW, evW_ι]
  exact hx l ζ

theorem app_of_mem (f : ↥(Frac0 (xplus X E hM) la G.w)) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) :=
  fun n => ⟨f, f.2, by rw [sub_self]; exact Ideal.zero_mem _⟩

theorem evL_inv (ζ : PtsG G la) {u : LamL (hsW hw)} (hu : IsUnit u) :
    evL (hsW hw) ζ ↑hu.unit⁻¹ = (evL (hsW hw) ζ u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, hu.val_inv_mul, map_one]

theorem inv_app {g0 : B.Cusp j wF} (C : CurveModel G la g0) (d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0) :
    (↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ : LamL (hsW hw)) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) := by
  obtain ⟨b, hb⟩ := (isUnit_toOsK_of_lift hw C d hd).exists_right_inv
  obtain ⟨v, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w b
  have hz : (1 - d * v : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_one, map_mul, hb, sub_self]
  have h := ιW_Jid hw hz
  push_cast at h
  exact appSub_inv _ _ _ d.2 v.2 h _

theorem inv_RG {g0 : B.Cusp j wF} (C : CurveModel G la g0) (d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w)) = 0)
    (hdi : HdIntAt (hsW hw) (d : Lw (xplus X E hM) la G.w)) :
    (↑(isUnit_of_lift_ne (hsW hw) (fun ζ => (hd ζ).1)).unit⁻¹ : LamL (hsW hw)) ∈ RGW hw := by
  refine ⟨stabSub_inv _ _ _ _ (stab_of_hdInt hw hdi) (fun ζ => ?_), inv_app hw C d (fun ζ => (hd ζ).1)⟩
  show 0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ _)
  rw [evL_inv, evW_ι]
  exact nval_inv_nonneg (hd ζ).1 (hd ζ).2

theorem mem_RG_of {g0 : B.Cusp j wF} (C : CurveModel G la g0) (f d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0 ∧
      vV (hsW hw ζ).T.V ((hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w)) = 0)
    (hfi : HdIntAt (hsW hw) (f : Lw (xplus X E hM) la G.w)) (hdi : HdIntAt (hsW hw) (d : Lw (xplus X E hM) la G.w)) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) *
      ↑(isUnit_of_lift_ne (hsW hw) (fun ζ => (hd ζ).1)).unit⁻¹ ∈ RGW hw :=
  (RGW hw).mul_mem ⟨stab_of_hdInt hw hfi, app_of_mem hw f⟩ (inv_RG hw C d hd hdi)

end Formalism.L2.Pj
