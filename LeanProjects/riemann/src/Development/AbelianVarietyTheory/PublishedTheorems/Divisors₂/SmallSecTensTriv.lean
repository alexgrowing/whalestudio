import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Published

def ArithHilbertSamuel : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
      (∀ᶠ m : ℕ in atTop, ((L.pow m).tens N).smallSec.Finite) ∧
      (fun m : ℕ => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) -
          a / ((D + 1).factorial : ℝ) * (m : ℝ) ^ (D + 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ (D + 1)

namespace ArithHilbertSamuel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

private theorem resG_resG {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

def secTensTriv (A : LB X) : A.Sec ≃ (tens A (LB.triv X)).Sec where
  toFun s := ⟨fun c => resG X inf_le_left (s.f c.1), fun c d => by
    have e := congrArg (resG X (U := A.U c.1 ⊓ A.U d.1)
      (V := (A.U c.1 ⊓ ⊤) ⊓ (A.U d.1 ⊓ ⊤)) (inf_le_inf inf_le_left inf_le_left)) (s.compat c.1 d.1)
    rw [map_mul, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    refine congrArg₂ (· * ·) ?_ (resG_resG _ _ _).symm
    simp only [tens, map_one, mul_one]
    rfl⟩
  invFun t := ⟨fun i => resG X (le_inf le_rfl le_top) (t.f (i, PUnit.unit)), fun i j => by
    have e := congrArg (resG X (U := (A.U i ⊓ ⊤) ⊓ (A.U j ⊓ ⊤)) (V := A.U i ⊓ A.U j)
      (inf_le_inf (le_inf le_rfl le_top) (le_inf le_rfl le_top))) (t.compat (i, PUnit.unit) (j, PUnit.unit))
    erw [map_mul, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    refine congrArg₂ (· * ·) ?_ (resG_resG _ _ _).symm
    simp only [tens, map_one, mul_one]
    exact (resG_resG _ _ _).trans (by simp [resG])⟩
  left_inv s := DVR.SecOps.sec_ext fun i => (resG_resG _ _ _).trans (by simp [resG])
  right_inv t := DVR.SecOps.sec_ext fun c => (resG_resG _ _ _).trans (by simp [resG]; rfl)

theorem nsq_secTensTriv (M : HermLB p) (s : M.B.Sec) (σ : k →+* ℂ) (y : CxPts p σ) :
    ((M.tens (HermLB.triv p)).φ σ).nsq (secVal p σ (secTensTriv M.B s)) y = (M.φ σ).nsq (secVal p σ s) y := by
  have hy := mem_pick ((M.tens (HermLB.triv p)).φ σ).isLB y
  rw [(M.φ σ).nsq_eq (secVal_mem s) (mem_ptsIn_inf.1 hy).1]
  exact congrArg₂ (fun a b => ‖a‖ ^ 2 * Real.exp (-b)) (ev_res _ hy _) (add_zero _)

theorem smallSec_tens_triv (M : HermLB p) :
    (M.tens (HermLB.triv p)).smallSec = secTensTriv M.B '' M.smallSec := by
  ext t
  obtain ⟨s, rfl⟩ := (secTensTriv M.B).surjective t
  refine Iff.trans ?_ (secTensTriv M.B).injective.mem_set_image.symm
  exact forall₂_congr fun σ y => by rw [nsq_secTensTriv]

variable [IsIntegral X] {L : HermLB p} {a : ℝ}

theorem of_triv (h : ArithHilbertSamuel) (hX : IsArithVar p D) (hL : L.IsNef D) (ha : L.IsSelfInter a) :
    (∀ᶠ m : ℕ in atTop, (L.pow m).smallSec.Finite) ∧
      (fun m : ℕ => Real.log ((L.pow m).smallSec.ncard : ℝ) -
          a / ((D + 1).factorial : ℝ) * (m : ℝ) ^ (D + 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ (D + 1) := by
  obtain ⟨h₁, h₂⟩ := h k X p D hX L (HermLB.triv p) a hL ha
  have e (m : ℕ) : ((L.pow m).tens (HermLB.triv p)).smallSec.ncard = (L.pow m).smallSec.ncard := by
    rw [smallSec_tens_triv]
    exact Set.ncard_image_of_injective _ (secTensTriv _).injective
  refine ⟨h₁.mono fun m hm => ?_, by simpa only [e] using h₂⟩
  rw [smallSec_tens_triv] at hm
  exact Set.Finite.of_finite_image hm (secTensTriv _).injective.injOn

theorem tendsto_of_triv (h : ArithHilbertSamuel) (hX : IsArithVar p D) (hL : L.IsNef D) (ha : L.IsSelfInter a) :
    Tendsto (fun m : ℕ => Real.log ((L.pow m).smallSec.ncard : ℝ) *
      (((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1))) atTop (𝓝 a) := by
  have hf : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h₁ := ((h.of_triv hX hL ha).2.tendsto_div_nhds_zero.mul_const ((D + 1).factorial : ℝ)).add_const a
  rw [zero_mul, zero_add] at h₁
  refine h₁.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem volNef (h : ArithHilbertSamuel) : VolNef := fun k _ X _ p D hX L a hL ha => by
  refine Tendsto.limsup_eq (((continuous_coe_real_ereal.tendsto a).comp
    (h.tendsto_of_triv hX hL ha)).congr' ?_)
  filter_upwards [(h.of_triv hX hL ha).1] with m hm
  have h0 : 0 < (L.pow m).smallSec.ncard := (Set.ncard_pos hm).2 ⟨_, (L.pow m).zero_mem_smallSec⟩
  rw [← hm.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
    ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul]
  rfl

end ArithHilbertSamuel

end GlobalTheory.Published
