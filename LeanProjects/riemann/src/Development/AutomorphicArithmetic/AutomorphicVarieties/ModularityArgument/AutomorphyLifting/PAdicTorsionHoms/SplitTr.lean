import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private UpperTheory.V.Af.RealLocalComponent.exists_comp UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
open private satLocFree from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
open private isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat

namespace UpperTheory.V.Z.Win.SplitTorusFixedPoints

open Matrix

section Transport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem smooth_comp (i : k ≃+* k') (hi' : Continuous i.symm) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) :=
  IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') h

private theorem plainTor_of_iso (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k') W}
    (hs : IsSmooth ρ) (hr : ρ.IsIrreducible) (hs' : IsSmooth ρ') (hr' : ρ'.IsIrreducible)
    (e : V ≃ₗ[ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' (GeneralLinearGroup.map i.toRingHom g) (e x))
    (h : GlobalTheory.RoadU.PlainTor (IrrGL.of ρ hs hr)) : GlobalTheory.RoadU.PlainTor (IrrGL.of ρ' hs' hr') := by
  obtain ⟨s, hS, h1, hU⟩ := h
  have hρ : HasSupport ρ s := hS.of_equiv (IrrGL.equivOf ρ hs hr).symm
  have hg : ∀ g : GL (Fin n) k',
      GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (ρ.comp (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) ρ' :=
    GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change e (ρ (GeneralLinearGroup.map i.symm.toRingHom g) x) = ρ' g (e x)
      rw [he, hg]⟩ e.bijective
  have h3 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hρ).of_equiv φ
  refine ⟨s.map (GlobalTheory.SuppIne.trGL i hi'), h3.of_equiv (IrrGL.equivOf ρ' hs' hr'), ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    exact h1 z hz
  · intro y hy z hz heq
    obtain ⟨y0, hy0, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z0, hz0, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨χ, hχ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y0 (h1 y0 hy0)
    obtain ⟨ψ, hψ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z0 (h1 z0 hz0)
    rw [GlobalTheory.DegOneChar.trGL_ofChar i hi' χ hχ (smooth_comp i hi' hχ),
      GlobalTheory.DegOneChar.trGL_ofChar i hi' ψ hψ (smooth_comp i hi' hψ), IrrGL.nu, IrrGL.tw_ofChar,
      IrrGL.ofChar_inj] at heq
    refine hU _ hy0 _ hz0 ?_
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    refine MonoidHom.ext fun t => ?_
    have h4 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
    have h5 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t :=
      Units.ext (i.symm_apply_apply _)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5,
      GlobalTheory.LocalFieldIso.absPow_map i hi] at h4
    exact h4

end Transport

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]

private theorem integers_symm {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (i : v.adicCompletion F ≃+* w.adicCompletion E) (hi' : Continuous i.symm) {y : w.adicCompletion E}
    (hy : y ∈ w.adicCompletionIntegers E) : i.symm y ∈ v.adicCompletionIntegers F := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hy' : Valued.v y ≤ 1 := hy
  change Valued.v (i.symm y) ≤ 1
  rw [← (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one] at hy' ⊢
  exact (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i.symm hi' y).2 hy'

private theorem hasFixed_of_iso {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (i : v.adicCompletion F ≃+* w.adicCompletion E) (hi' : Continuous i.symm) {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V}
    {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : V ≃ₗ[ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' (GeneralLinearGroup.map i.toRingHom g) (e x))
    (h : HasFixed ρ (GlobalTheory.LFun.KGL v n)) : HasFixed ρ' (GlobalTheory.LFun.KGL w n) := by
  obtain ⟨x, h0, hx⟩ := h
  refine ⟨e x, (map_ne_zero_iff e e.injective).2 h0, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hu
  have hm : GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom u ∈ GlobalTheory.LFun.KGL v n := by
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun a b => integers_symm i hi' (h1 a b), fun a b => ?_⟩
    rw [← map_inv]
    exact integers_symm i hi' (h2 a b)
  have hg : GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom u) = u :=
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  have := he (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom u) x
  rw [hx _ hm, hg] at this
  exact this.symm

end Fixed

end UpperTheory.V.Z.Win.SplitTorusFixedPoints

open UpperTheory.V.Z.Win.SplitTorusFixedPoints in
theorem UpperTheory.V.Z.Win.splitTr :
    SplitTr := by
  intro F E _ _ _ _ _ _ _ n _ π P hBC v w i hi
  have hi' : Continuous i.symm := GlobalTheory.LocalFieldIso.continuous_symm i hi.1
  have hsplit := hBC.split v w i hi.1 hi.2
  refine ⟨⟨fun h σ' hσ' => ?_, fun h σ hσ => ?_⟩, fun ⟨B, hB⟩ => ?_⟩
  · obtain ⟨σ, hσ⟩ := UpperTheory.V.Af.RealLocalComponent.exists_comp admissibleReal π v
    obtain ⟨e, he⟩ := hsplit σ σ' hσ hσ'
    exact plainTor_of_iso i hi.1 hi' _ _ _ _ e he (h σ hσ)
  · obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n P w
    obtain ⟨e, he⟩ := hsplit σ σ' hσ hσ'
    refine plainTor_of_iso i.symm hi' hi.1 _ _ _ _ e.symm (fun g x => ?_) (h σ' hσ')
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    congr 2
    exact (Units.ext (Matrix.ext fun _ _ => (i.apply_symm_apply _).symm) :
      g = Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g))
  · obtain ⟨σ, hσ⟩ := UpperTheory.V.Af.RealLocalComponent.exists_comp admissibleReal π v
    obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n P w
    obtain ⟨e, he⟩ := hsplit σ σ' hσ hσ'
    have h1 := ((satLocFree F n v σ).2 _ π.finPart (UpperTheory.V.Af.RealLocalComponent.isotypic π v σ hσ) B).1 hB
    obtain ⟨x, hx⟩ := h1.exists_vec
    have h2 : HasFixed σ.ρ (GlobalTheory.LFun.KGL v n) := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h1.1
      exact ⟨y, hy0, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk⟩
    obtain ⟨B', hB'⟩ := (satLocFree E n w σ').1 (hasFixed_of_iso i hi' e he h2)
    exact ⟨B', (CG.hasSat_mk _ _ _).2 (((satLocFree E n w σ').2 _ P.finPart (isotypic P w σ' hσ') B').2 hB')⟩
