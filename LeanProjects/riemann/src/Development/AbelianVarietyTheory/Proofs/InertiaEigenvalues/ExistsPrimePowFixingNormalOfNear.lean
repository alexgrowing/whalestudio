import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.PowFixNear
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  intro l _ F hF g hg
  haveI := F.2
  haveI : Normal ℚ_[l] ↥F.1 := hF
  have hpow : ∀ (i : ℕ) (x : Om l), x ∈ F.1 → x ≠ 0 → ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i x hx hx0
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hg x hx hx0
  have hst : ∀ (h : GQ l) (x : Om l), x ∈ F.1 → h x ∈ F.1 := by
    intro h x hx
    have e := AlgEquiv.restrictNormal_commutes h (↥F.1) ⟨x, hx⟩
    have e' : h x = (algebraMap (↥F.1) (Om l)) ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩) := e.symm
    rw [e']
    exact ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩).2
  set r := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) (↥F.1) with hr
  have hfin : IsOfFinOrder (r g) := isOfFinOrder_of_finite _
  set N := orderOf (r g) with hNdef
  have hN0 : N ≠ 0 := (hfin.orderOf_pos).ne'
  have hgN : ∀ x ∈ F.1, (g ^ N) x = x := by
    intro x hx
    have e := AlgEquiv.restrictNormal_commutes (g ^ N) (↥F.1) ⟨x, hx⟩
    have h1 : AlgEquiv.restrictNormal (g ^ N) (↥F.1) = 1 := by
      have := pow_orderOf_eq_one (r g)
      rw [← map_pow] at this
      exact this
    rw [h1] at e
    simpa using e.symm
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).ne_one
  refine ⟨s, fun y hy => ?_⟩
  refine GlobalTheory.TameInertiaCyclic.fix_of_near F (g ^ l ^ s) (hst _) (fun x hx hx0 => hpow _ x hx hx0) hN' (fun x hx => ?_) y hy
  rw [← pow_mul, ← hNe]
  exact hgN x hx

end GlobalTheory.PowFixNear
