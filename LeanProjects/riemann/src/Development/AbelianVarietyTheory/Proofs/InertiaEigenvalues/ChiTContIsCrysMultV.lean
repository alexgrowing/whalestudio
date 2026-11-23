import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc

theorem chiT_cont_isCrys_multV : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → TruncatedSeriesCountingIdentities.admG2 i r ρ π → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) τ (a + ((c : ℤ) - 1)) = multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ a := by
  intro D i r ρ π w hw C θ c h1 h2 hG2 hθc hθ
  set ψ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ := chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) with hψ
  have hsplit : ∀ g, ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    simp [tableLineDegreeTwo.charL, chiT, hψ]
  have hent : ∀ g, TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g 0 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    change TruncatedSeriesCountingIdentities.CoefExt.inc C (algebraMap _ _ ((D.nbr i w hw).eO
      (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    rfl
  let f : (Fin 1 → ↥C.LL.1) ≃ₗ[↥C.LL.1] ↥C.LL.1 := LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1
  have hf : ∀ g x, f (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)) g x) =
      Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) g (f x) := by
    intro g x
    show (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g).mulVec x 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • x 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, hent, smul_eq_mul]
  have cψ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ f hf (GlobalTheory.RestPtAssembly.chiRat_isCrys D i w hw C c h1 h2)
  have jψ : ∀ τ, IsJumpV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) τ ((c : ℤ) - 1) :=
    fun τ => GlobalTheory.HTW.isJumpV_of_injective _ _ _ f.toLinearMap f.injective hf τ _
      ((((hG2 w hw C).1.2.2.2.1 c h1 h2 τ ((c : ℤ) - 1))).2 rfl)
  have tw : IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ))
      (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) := by
    refine ⟨LinearEquiv.refl _ _, fun g x => ?_⟩
    simp only [Formalism.WeaklyAdmissibleFiltrations.charRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.refl_apply, smul_eq_mul, hsplit]
    ring
  obtain ⟨hcr, hm⟩ := GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL ↥C.LL.1 _ ↥C.LL.1 _ _ tw cψ hθ
  refine ⟨?_, hcr, fun τ a => hm τ a _ (jψ τ)⟩
  have hO : Continuous (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) := by
    have e : (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun h => ((D.nd.chi i c h : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i 1 h⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext h
      simp [chiU, map_inv]
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  have hi : Continuous (IntermediateField.inclusion C.le) :=
    continuous_induced_rng.2 continuous_subtype_val
  have hψc : Continuous fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) :=
    hi.comp (continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
      (hO.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)))))
  have e2 : (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) =
      fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := funext hsplit
  rw [e2]
  exact hψc.mul hθc

end GlobalTheory.UseLoc
