import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspAOfAb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_of_unr {y : WD h} (u : y.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : y.inePol σ = (X - 1) ^ y.lpDim := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.unr_mk] at u
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, u.2 ⟨σ, hσ⟩, LinearMap.charpoly_one]

theorem NcW.of_unr {y : WD h} (u : y.unr) : NcW y := by
  refine ⟨fun σ hσ => inePol_of_unr u (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), WD.unr_mono0 _ u, fun γ hγ _ z hz => ?_⟩
  rw [inePol_of_unr u hγ] at hz
  have h1 : ((X - 1 : ℂ[X]) ^ y.lpDim).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
  have h2 : z - 1 = 0 := by
    simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_one] at h1
    exact pow_eq_zero_iff (by rintro e; rw [e] at h1; simp at h1) |>.1 h1
  rw [sub_eq_zero.1 h2, one_pow]
end

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem nc_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Nc N A y ↔ NcW (T.e w y) := by
  refine and_congr ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩ (and_congr (T.mono0 w y)
    ⟨fun k γ hγ hc z hz => ?_, fun k γ hγ z hz => ?_⟩)
  · have hI := GlobalTheory.TameEig.wild_mem_Ine (E := H.E) _ σ hσ
    rw [← T.inePol w y σ hI, T.dim]
    exact k σ hI hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw
  · exact k γ ⟨hγ, hc⟩ z (by rwa [T.inePol w y γ hγ, ← T.dim])
  · exact k γ hγ.1 hγ.2 z (by rwa [← T.inePol w y γ hγ.1, T.dim])

theorem ncW_of_nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Nc N A y) : NcW (T.e w y) := (nc_iff T y).1 h

theorem relW_of_aw (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Aw (T.e w x) (T.e w y)) : RelW N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], fun u => (T.e w).injective (h.unr ((T.unr w y).1 u)), fun k σ hσ => ?_,
    fun k => (T.mono0 w x).2 (h.mono (ncW_of_nc T k))⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ,
    h.ine (ncW_of_nc T k) _ (deg_ineIncl _)]

theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : UpperTheory.GalN.Ab (T.e w x) (T.e w y)) : UpperTheory.GalN.CuspA N A x y := UpperTheory.GalN.cuspA_of_ab T h1 h

end UpperTheory.GalS
