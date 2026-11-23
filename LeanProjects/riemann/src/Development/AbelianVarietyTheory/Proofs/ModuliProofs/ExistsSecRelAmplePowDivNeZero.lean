import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDivSec

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def invLB (L : LB X) : LB X := ⟨L.1, L.U, fun i j => (L.g i j)⁻¹⟩

theorem isLB_invLB {L : LB X} (hL : L.IsLB) : (invLB L).IsLB where
  cover := hL.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hL.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hL.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h

theorem exists_sec_div (L M : LB X) (n t : ℕ) (u : LB.Sec (tw (invLB L) (lbPow M n) (t : ℤ))) :
    ∃ s : (LB.div (lbPow M (n * t)) L).Sec, nonzeroLocus u ≤ nonzeroLocus s := by
  have le : ∀ p : (PUnit → M.ι) × L.ι, powChart M p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ powChart M p.1 :=
    fun p y hy => ⟨hy.2, hy.1⟩
  let F : ∀ p : (PUnit → M.ι) × L.ι, Γ(X, powChart M p.1 ⊓ L.U p.2) := fun p =>
    resG X (le p) (show Γ(X, L.U p.2 ⊓ powChart M p.1) from u.f (p.2, p.1))
  have hF : ∀ (y : X) (p : (PUnit → M.ι) × L.ι), y ∈ powChart M p.1 ⊓ L.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f (p.2, p.1)) := fun y p hy => gs_res (𝟙 X) y (le p) hy _
  refine ⟨secOfGerm (M := LB.div (lbPow M (n * t)) L) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · have e₁ := gs_compat u (𝟙 X) y (j := (p.2, p.1)) (j' := (q.2, q.1)) (le p hp) (le q hq)
    have e₂ := TwistGen.gm_tw_g (invLB L) (lbPow M n) t y (p.2, p.1) (q.2, q.1) (le p hp) (le q hq)
    have e₃ := gm_lbPow_g (L := M) n (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₄ := gm_lbPow_g (L := M) (n * t) (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₅ := gm_div L (lbPow M (n * t)) (𝟙 X) y p q ⟨hp, hq⟩
    have e₆ : gm (𝟙 X) y ((invLB L).U p.2 ⊓ (invLB L).U q.2) ((invLB L).g p.2 q.2) =
        (gm (𝟙 X) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := map_inv _ _
    rw [e₄] at e₅
    dsimp only at e₂
    rw [e₃, e₆] at e₂
    refine (hF y p hp).trans (e₁.trans (congrArg₂ (· * ·) (e₂.trans ?_) (hF y q hq).symm))
    refine Eq.trans ?_ (congrArg Units.val e₅).symm
    rw [Units.val_mul, pow_mul, _root_.mul_comm]
    simp only [Units.val_pow_eq_pow_val]
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hp' : y ∈ powChart M p.2 ⊓ L.U p.1 := ⟨hp.2, hp.1⟩
    refine (mem_nonzeroLocus_iff_isUnit (M := LB.div (lbPow M (n * t)) L) _ (k := (p.2, p.1)) hp').2 ?_
    exact (congrArg IsUnit (hF y (p.2, p.1) hp')).mpr ((mem_nonzeroLocus_iff_isUnit u hp).1 hy)

theorem exists_sec_div_mem {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M) (x : X) :
    ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ x ∈ nonzeroLocus s := by
  have := hM.compactSpace
  have := hM.quasiSeparatedSpace
  obtain ⟨n, hn, σ, hx, ha⟩ := hM.exists_affine x
  obtain ⟨V, N, hV, h⟩ := TwistGen.exists_nhds (isLB_invLB hL) (isLB_lbPow hM.isLB n) σ ha x hx
  obtain ⟨u, hu⟩ := h 1
  obtain ⟨s, hs⟩ := exists_sec_div L M n (N + 1) u
  exact ⟨_, s, Nat.mul_pos hn (Nat.succ_pos N), hs (hu hV)⟩

theorem exists_sec_pow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  intro K _ A L M _ ⟨x⟩ hL hM hA
  obtain ⟨a, s, ha, hx⟩ := exists_sec_div_mem hL (isAmpleLB_of_relAmple_of_isAffine A hM hA) x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨a, s, ha, j, fun h => ?_⟩
  rw [h, Scheme.basicOpen_zero] at hj
  exact hj

end GlobalTheory.AmpleDivSec
