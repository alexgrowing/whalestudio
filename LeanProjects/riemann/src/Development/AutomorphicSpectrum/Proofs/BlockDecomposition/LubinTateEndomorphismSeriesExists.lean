import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTPer

theorem map_subst_comm {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) {F G : PowerSeries A}
    {F' : PowerSeries B} (hF' : PowerSeries.map h F = F')
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0)
    (hs : PowerSeries.subst G F = PowerSeries.subst F G) :
    PowerSeries.subst (PowerSeries.map h G) F' = PowerSeries.subst F' (PowerSeries.map h G) := by
  subst hF'
  have h2 := congrArg (MvPowerSeries.map h) hs
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)] at h2
  exact h2

open GlobalTheory.CompanionTheory.LTHodge.CharEx GroundTheory.LocalField GroundTheory.LocalField.FormalGroup ValuativeRel in

theorem exists_series_comm : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  intro l _ K π hπ a
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let e : ↥(OL K) ≃+* 𝒪[↥K.1] := intEquiv K
  let es : 𝒪[↥K.1] →+* ↥(OL K) := (e.symm : 𝒪[↥K.1] →+* ↥(OL K))
  have hp : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hf := isLubinTateSeries_ltPoly (e π)
  have hm := map_ltSeries K hp
  have hes : (intEquiv K).symm (e π) = π := e.symm_apply_apply π
  rw [hes] at hm
  have hF : PowerSeries.map es (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = ltSeries π := by
    rw [← hm]
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  have hF0 : PowerSeries.constantCoeff (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = 0 :=
    hf.constantCoeff_eq_zero
  let h := lubinTateHom hp hf hf (e a)
  have h0 : PowerSeries.constantCoeff h.toPowerSeries = 0 := h.constantCoeff_eq_zero
  have h1 : PowerSeries.coeff 1 h.toPowerSeries = e a := coeff_one_lubinTateHom hp hf hf (e a)
  have hs := subst_lubinTateHom hp hf hf (e a)
  refine ⟨PowerSeries.map es h.toPowerSeries, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
    exact e.symm_apply_apply a
  · exact map_subst_comm es hF hF0 h0 hs

end GlobalTheory.CompanionTheory.LTPer
