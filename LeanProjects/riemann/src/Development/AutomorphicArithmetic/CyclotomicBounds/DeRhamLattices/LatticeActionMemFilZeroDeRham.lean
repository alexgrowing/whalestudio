import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.latticeAction_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (d : OD l ↥(OL LL)) (v : T.V), act d (v ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) := by
  intro l _ LL T Pl AI Td act hact d v
  have hfil := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    rw [hact, mul_one]
    have hb : (JumpDR.cD Td) b ∈ (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0 := (hfil _).2 ⟨b, rfl⟩
    rw [FilV.eq_1]
    exact ⟨((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] ⟨_, hb⟩, by simp⟩
  | add x y hx hy =>
    rw [map_add, AddMonoidHom.add_apply]
    exact Submodule.add_mem _ hx hy
