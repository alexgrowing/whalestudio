import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegScalar

theorem absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) : absPow k (n : ℂ) = absPow k 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, absPow_add, ih, pow_succ]

theorem absPow_pow_comm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (t : kˣ) :
    (((absPow k (a : ℂ) ^ d) t : ℂˣ) : ℂ) = ((absPow k (d : ℂ) t : ℂˣ) : ℂ) ^ a := by
  rw [absPow_natCast, absPow_natCast, ← pow_mul, mul_comm a d, MonoidHom.pow_apply, MonoidHom.pow_apply, pow_mul,
    Units.val_pow_eq_pow_val]

theorem prod_mul_pow (l : ℕ) (c e : ℂ) :
    ∏ a : Fin l, (c * e ^ (a : ℕ)) = c ^ l * e ^ (l * (l - 1) / 2) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => c * e ^ a) l, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

theorem scalarBy_of_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Segment k) (y : IrrGL k) : IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c →
      Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  intro hL t c hc
  obtain ⟨hd, -, f, hf, -⟩ := hL
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Γ.first.2.rep.smooth Γ.first.2.rep.irr
  have hωc : ((ω t : ℂˣ) : ℂ) = c := by
    haveI := Model.nontrivial_of_isIrreducible Γ.first.2.rep.irr
    obtain ⟨w, hw⟩ := exists_ne (0 : Γ.first.2.rep.V)
    have h1 : ((ω t : ℂˣ) : ℂ) • w = c • w := (hω t w).symm.trans (hc w)
    exact smul_left_injective ℂ hw h1
  have hterm : ∀ a : Fin Γ.len, HasCentralChar (Γ.term a).rep (ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) :=
    fun a => UnitaryOrder.hasCentralChar_nu Γ.first hω ((a : ℕ) : ℂ)
  have hsc : ∀ v, y.rep (Matrix.GeneralLinearGroup.scalar (Fin y.1) t) v =
      (∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Γ.term a).1) hd)
      (fun a => (Γ.term a).rep) _ hterm t w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  have h2 : ∏ a : Fin Γ.len, ((((ω * absPow k ((a : ℕ) : ℂ) ^ Γ.first.1) t : ℂˣ)) : ℂ) =
      c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2) := by
    rw [← prod_mul_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul, hωc, absPow_pow_comm]
  rw [← h2]
  exact hsc

end GlobalTheory.CompanionTheory.SegScalar

end
