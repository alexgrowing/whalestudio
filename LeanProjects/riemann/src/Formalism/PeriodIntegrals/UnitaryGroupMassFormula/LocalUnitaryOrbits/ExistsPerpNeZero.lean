import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TwoNeZeroV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem hR_smul_right_F (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v) :
    hR (Fv F v) σ J x (c • w) = c • hR (Fv F v) σ J x w := by
  rw [← algebraMap_smul (Fv F v ⊗[F] E) c w, hR_smul_right, Algebra.smul_def]

def perpMap {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) where
  toFun w i := hR (Fv F v) σ J (X i) w
  map_add' x y := funext fun i => hR_add_right' σ J v (X i) x y
  map_smul' c w := funext fun i => hR_smul_right_F σ J v (X i) w c

theorem exists_perp_ne_zero (hcm : IsCMExt F E σ) {ι : Type} [Fintype ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hc : Fintype.card ι < n) : ∃ w : Fin n → Fv F v ⊗[F] E, w ≠ 0 ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0 := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have hlt : Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E) < Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := perpMap σ J v X) hlt
  obtain ⟨w, hw, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.1 hw) i⟩

theorem primPerp_holds : PrimPerp σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = b i := fun i => Module.Basis.mk_apply hli hsp i
  have hsymm : ∀ c : Fin m → Fv F v, B.equivFun.symm c = ∑ i, c i • b i := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp only [hB]
  obtain ⟨w, hw0, hwp⟩ := exists_perp_ne_zero σ J v hstd.1 X hc
  set c := B.equivFun w with hcdef
  have hcw : w = ∑ i, c i • b i := by rw [← hsymm, hcdef, LinearEquiv.symm_apply_apply]
  have hcne : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    rw [hcw]
    simp [h]
  obtain ⟨i0, hi0⟩ := hcne
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) hne
  have hcj : c j ≠ 0 := by
    intro h
    have h1 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le'))
  have hvj : Valued.v (c j) ≠ 0 := (Valuation.ne_zero_iff _).2 hcj
  set p := (c j)⁻¹ • w with hp
  have hcp : B.equivFun p = (c j)⁻¹ • c := by rw [hp, map_smul]
  have hpmem : p ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
    refine (hmem p).2 ⟨fun i => ⟨(c j)⁻¹ * c i, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      calc (Valued.v (c j))⁻¹ * Valued.v (c i) ≤ (Valued.v (c j))⁻¹ * Valued.v (c j) :=
            mul_le_mul' le_rfl (hj i (Finset.mem_univ _))
        _ = 1 := inv_mul_cancel₀ hvj
    · rw [← hsymm]
      change p = B.equivFun.symm ((c j)⁻¹ • c)
      rw [← hcp, LinearEquiv.symm_apply_apply]
  refine ⟨ϖ, hϖ, p, ⟨hpmem, fun i => ?_⟩, ?_⟩
  · rw [hp, hR_smul_right_F, hwp i, smul_zero]
  · intro hin
    rw [sc_eq, algebraMap_smul] at hin
    obtain ⟨d, hd⟩ := (hmem _).1 hin
    have hd' : ϖ⁻¹ • p = B.equivFun.symm (fun i => (d i : Fv F v)) := by rw [hsymm]; exact hd
    have hcoord := congrFun (congrArg B.equivFun hd') j
    rw [LinearEquiv.apply_symm_apply, map_smul, hcp] at hcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    rw [inv_mul_cancel₀ hcj, mul_one] at hcoord
    have hint : ϖ⁻¹ ∈ v.adicCompletionIntegers F := by rw [hcoord]; exact (d j).2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hint
    have h1 : Valued.v (ϖ * ϖ⁻¹) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hv]
      calc WithZero.exp (-1 : ℤ) * Valued.v ϖ⁻¹ ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl hint
        _ = _ := mul_one _
    rw [mul_inv_cancel₀ hϖ0, map_one] at h1
    exact absurd h1 (by decide)

end PI.OmLocU.UnN
