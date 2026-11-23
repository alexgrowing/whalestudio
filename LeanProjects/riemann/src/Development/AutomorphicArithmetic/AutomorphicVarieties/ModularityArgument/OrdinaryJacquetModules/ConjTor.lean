import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord

section Loc

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨m, x, hs, hirr, hcusp, e, hsub⟩ := h
  have hπs : GlobalTheory.PRep.IsSmooth π := HasSupport.isSmooth ⟨m, x, hs, hirr, hcusp, e, hsub⟩
  have key : IsCuspSupport (contra π) (fun a => (x a).fst) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N)
      (hA k N V π hπs hirr) hirr, fun a => ?_, e, ?_⟩
    · have hc := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hcusp a).1, (hcusp a).2.2⟩).1
      rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.isCusp_of] at hc
      exact ⟨(hcusp a).1, GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a), hc.2⟩
    · have hρs : GlobalTheory.PRep.IsSmooth (piTensor fun a => (x a).rep) :=
        isSmooth_piTensor fun a => (x a).snd.rep.smooth
      have h1 := GlobalTheory.CompanionTheory.ContraSub.main k N V _ π (parInd e (piTensor fun a => (x a).rep)) hπs
        (isSmooth_parInd e _) hsub
      have h2 : Nonempty ((parInd e (piTensor fun a => contra (x a).rep)).Equiv
          (contra (parInd e (piTensor fun a => (x a).rep)))) :=
        GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra (σ := piTensor fun a => contra (x a).rep)
          (ρ := piTensor fun a => (x a).rep) e hρs (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
      obtain ⟨E⟩ := h2
      have h3 : IsSubquotient (contra (parInd e (piTensor fun a => (x a).rep)))
          (parInd e (piTensor fun a => contra (x a).rep)) :=
        IsSubquotient.of_surjective E.toIntertwiningMap fun w => ⟨E.invFun w, E.right_inv w⟩
      exact IsSubquotient.trans h1 h3
  have hsupp := hasSupport_of_isCuspSupport key
  have hmap : s.map Zc.dualCl = Multiset.map (fun a => Zc.dualCl (x a)) Finset.univ.val := by
    rw [← hs, Multiset.map_map]
    rfl
  rw [hmap]
  simp only [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  exact hsupp

private theorem hasSupport_of_invT (c : k ≃+* k') (hc : Continuous c) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k') W)
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g v, τ (GlobalTheory.LFun.ConjPlace.invT c N g) (T v) = T (σ g v))
    {s : Multiset (IrrGL k)} (h : HasSupport σ s) :
    HasSupport τ ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL c (GlobalTheory.LocalFieldIso.continuous_symm c hc))) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm c hc
  obtain ⟨E⟩ := GlobalTheory.GelfandKazhdan.equiv_contra k N V σ (hA k N V σ h.isSmooth h.isIrreducible) h.isIrreducible
  have h1 := (hasSupport_contra h).of_equiv E.symm
  have h2 := GlobalTheory.SuppIne.hasSupport_comp c hc hc' h1
  refine h2.of_equiv (GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩ T.bijective)
  have hg : GlobalTheory.LFun.ConjPlace.invT c N (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k
      (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) = g :=
    Units.ext (Matrix.ext fun i j => by
      rw [GlobalTheory.LFun.ConjPlace.invT_val]
      exact c.apply_symm_apply _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change T (σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) v) = τ g (T v)
  rw [← hT, hg]

private theorem dualCl_eq_of {x y : IrrGL k} (H : GlobalTheory.LocLanglands.DualCl x y) : Zc.dualCl x = y := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨n, π, π', rfl, rfl, ⟨E⟩⟩ := H
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  change IrrGL.of _ _ _ = IrrGL.of π'.ρ π'.smooth π'.irr
  exact IrrGL.of_eq_of.2 ⟨(GlobalTheory.ContraRefl.contraEquiv (equivRep π)).trans E.symm⟩

private theorem val_lt_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) < 1 ↔ valuation k x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x⁻¹
  have p1 : 0 < valuation k x := by
    rw [zero_lt_iff]; simpa using hx
  have p2 : 0 < valuation k' (i x) := by
    rw [zero_lt_iff]; simpa using hx
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ p1, inv_le_one₀ p2] at h
  rw [← not_le, ← not_le, h]

private theorem val_eq_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) = 1 ↔ valuation k x = 1 := by
  have a := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x
  have b := val_lt_one_iff i hi x
  exact ⟨fun h => le_antisymm (a.1 h.le) (not_lt.1 fun l => (b.2 l).ne h),
    fun h => le_antisymm (a.2 h.le) (not_lt.1 fun l => (b.1 l).ne h)⟩

private theorem unram_unif (i : k ≃+* k') (hi : Continuous i) (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    μ (Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k')) = μ (ImaginaryQuadraticEtaCharacter.unif k) := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  set a : kˣ := Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k') with ha
  have hav : (a : k) = i.symm (ImaginaryQuadraticEtaCharacter.unif k' : k') := rfl
  have S := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  have S' := (ImaginaryQuadraticEtaCharacter.polFacts k').1
  have ha1 : valuation k (a : k) < 1 := by
    rw [hav]; exact (val_lt_one_iff i.symm hi' _).2 S'.1
  have hb1 : valuation k' (i (ImaginaryQuadraticEtaCharacter.unif k : k)) < 1 := (val_lt_one_iff i hi _).2 S.1
  have le1 := S.2 _ ha1
  have le2 := S'.2 _ hb1
  have pa : 0 < valuation k (a : k) := by
    rw [zero_lt_iff]; simp
  have pb : 0 < valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := by
    rw [zero_lt_iff]; simp
  have pu : 0 < valuation k' (ImaginaryQuadraticEtaCharacter.unif k' : k') := by
    rw [zero_lt_iff]; simp
  have le3 : valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) ≤ valuation k (a : k) := by
    have h1 : valuation k' (i ((ImaginaryQuadraticEtaCharacter.unif k : k) * (a : k)⁻¹)) ≤ 1 := by
      have : i (a : k) = (ImaginaryQuadraticEtaCharacter.unif k' : k') := by rw [hav]; exact i.apply_symm_apply _
      rw [map_mul, map_inv₀, this, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ le2 zero_le'
    have h2 := (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi _).1 h1
    rw [map_mul, map_inv₀] at h2
    simpa using (mul_inv_le_iff₀ pa).1 h2
  have he : valuation k (a : k) = valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := le_antisymm le1 le3
  have hu : μ (a * (ImaginaryQuadraticEtaCharacter.unif k)⁻¹) = 1 := hμ _ (by
    rw [Units.val_mul, map_mul, he, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ pb.ne'])
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu

private theorem isUnram_comp (i : k ≃+* k') (hi : Continuous i) {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) :
    IsUnram (μ.comp (Units.map i.symm.toRingHom.toMonoidHom)) := fun x hx =>
  hμ _ ((val_eq_one_iff i.symm (GlobalTheory.LocalFieldIso.continuous_symm i hi) _).2 hx)

private theorem unl_of_map (i : k ≃+* k') (hi : Continuous i) (q : ℕ) (s : Multiset (IrrGL k))
    (h : ImaginaryQuadraticEtaCharacter.Unl q ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i (GlobalTheory.LocalFieldIso.continuous_symm i hi)))) :
    ImaginaryQuadraticEtaCharacter.Unl q s := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  intro ξ hξ ξ' hξ' hun
  obtain ⟨h1, m1⟩ := hξ
  obtain ⟨h2, m2⟩ := hξ'
  let U : k'ˣ →* kˣ := Units.map i.symm.toRingHom.toMonoidHom
  have sm : ∀ ζ : kˣ →* ℂˣ, IsSmoothChar ζ → IsSmoothChar ((ζ⁻¹).comp U) := fun ζ hζ =>
    IsOpen.preimage (Continuous.units_map _ hi') hζ.inv
  have mem : ∀ (ζ : kˣ →* ℂˣ) (hζ : IsSmoothChar ζ), IrrGL.ofChar ζ hζ ∈ s →
      IrrGL.ofChar ((ζ⁻¹).comp U) (sm ζ hζ) ∈ (s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i hi') := fun ζ hζ hm =>
    Multiset.mem_map.2 ⟨IrrGL.ofChar ζ⁻¹ hζ.inv, Multiset.mem_map.2 ⟨_, hm,
      dualCl_eq_of (GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ hζ hζ.inv rfl)⟩,
      GlobalTheory.DegOneChar.trGL_ofChar i hi' _ _ _⟩
  have e : ((ξ'⁻¹).comp U) * ((ξ⁻¹).comp U)⁻¹ = (ξ * ξ'⁻¹).comp U :=
    MonoidHom.ext fun x => by simp [mul_comm]
  have := h ((ξ'⁻¹).comp U) ⟨sm _ h2, mem _ _ m2⟩ ((ξ⁻¹).comp U) ⟨sm _ h1, mem _ _ m1⟩
    (by rw [e]; exact isUnram_comp i hi hun)
  rw [e, MonoidHom.comp_apply] at this
  rwa [unram_unif i hi _ hun] at this

end Loc

end UpperTheory.V.Z.Ord
