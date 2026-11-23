import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PtBBasic

open Formalism.FourierDecayAlt.P.TLB

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nv_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {s : ℂ} (h : MulAt x T s)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : nv (T Φ) x = ‖s‖ * nv Φ x := by
  unfold nv
  rw [h Φ, ← norm_smul]
  rfl

theorem nv_nonneg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : 0 ≤ nv Φ x := norm_nonneg _

theorem ptB_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (b : RA P Bs) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', ∃ s : ℂ, MulAt x b.1 s ∧ ‖s‖ ≤ C) : PtB P Bs b := by
  refine ⟨C, hC, fun Φ x hx => ?_⟩
  obtain ⟨s, hs, hle⟩ := h x hx
  rw [nv_of_mulAt hs]
  exact mul_le_mul_of_nonneg_right hle (nv_nonneg Φ x)

theorem ptB_mul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (a b : RA P Bs) (ha : PtB P Bs a) (hb : PtB P Bs b) :
    PtB P Bs (a * b) := by
  obtain ⟨C, hC, ha⟩ := ha
  obtain ⟨C', hC', hb⟩ := hb
  refine ⟨C * C', mul_nonneg hC hC', fun Φ x hx => ?_⟩
  rw [pr_mul_fst, Module.End.mul_apply, mul_assoc]
  exact (ha _ x hx).trans (mul_le_mul_of_nonneg_left (hb Φ x hx) hC)

theorem norm_ratio_le (a b : ℂ) (h : ‖a‖ = ‖b‖) : ‖a * b⁻¹‖ ≤ 1 := by
  rw [norm_mul, norm_inv, h]
  exact mul_inv_le_one

theorem sqrt_lt_zeta {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    Real.sqrt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') < ‖Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2‖ := by
  have h := hx.2.2
  unfold Q.GGl at h
  rw [Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)
  rw [← Real.sqrt_sq hn]
  exact Real.sqrt_lt_sqrt (mul_pos Bs.T_pos Bs.T'_pos).le (by linarith)

end GlobalTheory.HatNF.PtBBasic

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt.P.TLB PtBBasic

theorem ptB_basic : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → (PtB P Bs 1 ∧ (∀ a b, PtB P Bs a → PtB P Bs b → PtB P Bs (a * b))) ∧ PtB P Bs d.L.ζi ∧ PtB P Bs d.L.ζbi ∧ PtB P Bs (d.L.D * d.L.Dbi) ∧ PtB P Bs (d.L.Db * d.L.Di) ∧ PtB P Bs (d.L.Drb * d.L.Dri) ∧ PtB P Bs (d.L.Dr * d.L.Drbi) ∧ ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < dR P Bs x.1 x.2 ∧ 0 < gR P Bs x.1 x.2 ∧ nv (d.L.Di.1 Φ) x = (dR P Bs x.1 x.2)⁻¹ * nv Φ x ∧ nv ((TL.gI d.L).1 Φ) x = (gR P Bs x.1 x.2)⁻¹ * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X μ L0 st l0 d _ hd
  have hL := hd.1
  set L := d.L with hLdef
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, x.1 a)⁻¹ := fun x => by
    rw [← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (star (∏ a, x.1 a)) := fun x => by
    rw [star_prod]
    exact mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (star (∏ a, x.1 a))⁻¹ := fun x => by
    rw [star_prod, ← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have hD : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.D.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) :=
    fun x hx => mulAt_mul (hDr x) (hz x hx)
  have hDb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Db.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx
    rw [star_mul']
    exact mulAt_mul (hDrb x) (hzb x hx)
  have hDi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Di.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx
    rw [mul_inv, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  have hDbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Dbi.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx
    rw [star_mul', mul_inv, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  have hsq : 0 < Real.sqrt (Tz Pa.k Pa.r Bs.z * Tz Pa.k Pa.r Bs.z') :=
    Real.sqrt_pos.2 (mul_pos Bs.T_pos Bs.T'_pos)
  refine ⟨⟨?_, ptB_mul⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ => ⟨1, mulAt_one x, by simp⟩
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzi x hx, ?_⟩
    rw [norm_inv]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzbi x hx, ?_⟩
    rw [norm_inv, norm_star]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hD x hx) (hDbi x hx), norm_ratio_le _ _ (norm_star _).symm⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hDb x hx) (hDi x hx), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDrb x) (hDri x), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDr x) (hDrbi x), norm_ratio_le _ _ (norm_star _).symm⟩
  · intro Φ x hx
    have hc : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
    have hζ : Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2 ≠ 0 :=
      norm_pos_iff.1 (hsq.trans (sqrt_lt_zeta Bs hx))
    have hG := hx.2.2
    refine ⟨norm_pos_iff.2 (mul_ne_zero hc hζ), mul_pos (Complex.normSq_pos.2 hc) hG, ?_, ?_⟩
    · rw [nv_of_mulAt (hDi x hx), norm_inv]
      rfl
    · have h : MulAt x (TL.gI L).1 _ := mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
      rw [nv_of_mulAt h]
      congr 1
      unfold gR
      rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, norm_star, Complex.norm_real, Real.norm_of_nonneg hG.le,
        Complex.normSq_eq_norm_sq, sq, mul_inv, mul_inv]

end GlobalTheory.HatNF
