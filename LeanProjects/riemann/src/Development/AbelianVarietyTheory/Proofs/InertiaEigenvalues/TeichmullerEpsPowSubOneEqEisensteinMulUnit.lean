import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem teich_pow_sub_one_eq_ED_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ε c hε hc
  have hd : ED K t ϖ = toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) := by
    rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨⟨ξ, hξ, hμ⟩, -, hθδ, -⟩ := (GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  set G : Ainf l := ∑ i ∈ Finset.range c, WittVector.teichmuller l ε ^ i with hG
  set w : Ainf l := (v : Ainf l) * (muOf δ * G) with hwdef
  have hkey : WittVector.teichmuller l ε ^ c - 1 = ϖ.ev a (eis l a e) * w := by
    have h1 : WittVector.teichmuller l ε ^ c - 1 = muOf ε * G := by
      rw [muOf, hG, mul_comm, geom_sum_mul]
    rw [h1, hμ, ← hv, hwdef]
    ring
  have hθG : ((Per.θ l G : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
    rw [hG, map_sum]
    simp only [map_pow, WittVector.fontaineTheta_teichmuller, hε.1, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have hθw : ((Per.θ l w : Per.OC l) : ℂ_[l]) ≠ 0 := by
    have h1 : ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
      (v.isUnit.map (Per.θ l)).ne_zero (Subtype.ext (h.trans rfl))
    have h2 : ((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h => hθδ (Subtype.ext (h.trans rfl))
    have h3 : (c : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc
    have h4 : ((Per.θ l w : Per.OC l) : ℂ_[l]) =
        ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) * (((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) *
          ((Per.θ l G : Per.OC l) : ℂ_[l])) := by
      rw [hwdef, map_mul, map_mul]
      rfl
    rw [h4, hθG]
    exact mul_ne_zero h1 (mul_ne_zero h2 h3)
  have hwu : IsUnit (ainfToBdRp l w) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
    change Per.θD l (GlobalTheory.MemLoc.aDp l w) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact hθw)
  refine ⟨toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O), ?_, ?_⟩
  · have h2 : toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O) =
        (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O) (ainfToBdRp l w) := by
      simp [toOD]
    rw [h2]
    exact hwu.map _
  · have h3 : ((1 : O) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ε : OA l O) ^ c - 1 =
        ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) * ((1 : O) ⊗ₜ[ℤ_[l]] w) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hkey,
        Algebra.TensorProduct.one_def, TensorProduct.tmul_sub]
    rw [hd, ← map_mul, ← h3, map_sub, map_pow, map_one]

end GlobalTheory.GalStep
