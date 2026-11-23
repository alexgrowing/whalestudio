import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

theorem ED_eq (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) := by
  rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem σA_ev_eis_eq {e : ℕ} [NeZero e] (ϖ : PiSys l e) (g : GQ l) :
    ∃ u : Ainf l, IsUnit u ∧ Per.σA g (ϖ.ev 1 (eis l 1 e)) = ϖ.ev 1 (eis l 1 e) * u := by
  set d := ϖ.ev 1 (eis l 1 e) with hd
  have hdvd : ∀ h : GQ l, d ∣ Per.σA h d := fun h => by
    rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]
  obtain ⟨u, hu⟩ := hdvd g
  obtain ⟨u', hu'⟩ := hdvd g⁻¹
  by_cases hd0 : d = 0
  · refine ⟨1, isUnit_one, ?_⟩
    rw [hd0, map_zero, zero_mul]
  · refine ⟨u, ?_, hu⟩
    have h1 : d = d * (u * Per.σA g u') := by
      calc d = Per.σA g (Per.σA g⁻¹ d) := by rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]
        _ = d * (u * Per.σA g u') := by rw [hu', map_mul, hu, mul_assoc]
    have h2 : u * Per.σA g u' = 1 := by
      have h3 : d * (u * Per.σA g u' - 1) = 0 := by rw [mul_sub, ← h1, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hd0)
    exact IsUnit.of_mul_eq_one _ h2

end GlobalTheory.GalStep

open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.galOD_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g _
  obtain ⟨u, hu, hσ⟩ := σA_ev_eis_eq ϖ g
  refine ⟨(1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l u, ?_, ?_⟩
  · exact hu.map ((Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O).comp (ainfToBdRp l))
  · rw [ED_eq a e O K t ϖ]
    change (1 : O) ⊗ₜ[ℤ_[l]] Per.σDp g (GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e))) = _
    rw [GlobalTheory.MemLoc.ActLaws.σDp_aDp, hσ, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
