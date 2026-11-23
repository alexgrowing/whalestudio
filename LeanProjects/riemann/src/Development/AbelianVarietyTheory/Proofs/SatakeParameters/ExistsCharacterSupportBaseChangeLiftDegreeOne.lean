import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtOneOfContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneChar

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem detChar_map (i : k ≃+* k') (χ : kˣ →* ℂˣ) (g : GL (Fin 1) k') :
    detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) =
      detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) g := by
  simp only [detChar_apply, MonoidHom.comp_apply]
  congr 1
  ext
  simp [RingHom.map_det]

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom))) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) h' := by
  unfold GlobalTheory.SuppIne.trGL
  change _ = IrrGL.of (IrrRep.det (Fin 1) _ h').ρ (IrrRep.det (Fin 1) _ h').smooth (IrrRep.det (Fin 1) _ h').irr
  refine IrrGL.of_eq_of.2 ⟨?_⟩
  let E := (equivRep (IrrRep.det (Fin 1) χ hχ)).symm
  refine GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun x => ?_⟩ E.toLinearEquiv.bijective
  have h1 := LinearMap.congr_fun (E.isIntertwining' (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)) x
  change E.toLinearEquiv ((IrrRep.det (Fin 1) χ hχ).cl.rep.ρ _ x) = _
  refine h1.trans ?_
  change ((detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) : ℂˣ) : ℂ) • E.toLinearEquiv x =
    ((detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (g : GL (Fin 1) k') : ℂˣ) : ℂ) • E.toLinearEquiv x
  exact congrArg (fun z : ℂˣ => (z : ℂ) • E.toLinearEquiv x) (detChar_map i χ g)

end Char

section Norm

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem adicCompletionMap_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (z : v.adicCompletion K) :
    GroundTheory.Global.adicCompletionMap v u z = cLoc hO z :=
  congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer
    (GroundTheory.Global.continuous_adicCompletionMap v u) (continuous_cLoc hO)
    (funext fun x => (GroundTheory.Global.adicCompletionMap_algebraMap v u x).trans
      (by rw [Function.comp_apply, cLoc_algebraMap hO x, he]))) z

theorem normU_apply (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (y : (u.adicCompletion M)ˣ) :
    ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (locEquiv hO).symm y := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have hf : ∀ z, algebraMap (v.adicCompletion K) (u.adicCompletion M) z = locEquiv hO z :=
    adicCompletionMap_eq e he hO
  have hb : Function.Bijective (algebraMap (v.adicCompletion K) (u.adicCompletion M)) := by
    have : ⇑(algebraMap (v.adicCompletion K) (u.adicCompletion M)) = locEquiv hO := funext hf
    rw [this]
    exact (locEquiv hO).bijective
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb
  obtain ⟨z, hz⟩ := hb.2 (y : u.adicCompletion M)
  change Algebra.norm (v.adicCompletion K) (y : u.adicCompletion M) = _
  rw [← hz, Algebra.norm_algebraMap, h1, pow_one, hf, RingEquiv.symm_apply_apply]

theorem normU_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) :
    GlobalTheory.BCChar.normU v u = Units.map (locEquiv hO).symm.toRingHom.toMonoidHom :=
  MonoidHom.ext fun y => Units.ext (normU_apply e he hO y)

theorem over_of_liesOver (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [h : u.asIdeal.LiesOver v.asIdeal] : Over e v u := fun x => by
  have hx : RingOfIntegers.mapRingEquiv e x = algebraMap (𝓞 K) (𝓞 M) x := RingOfIntegers.ext (he x)
  rw [hx, h.over, Ideal.under_def, Ideal.mem_comap]

end Norm

section Lift

theorem ofChar_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ ψ : kˣ →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : IrrGL.ofChar χ hχ = IrrGL.ofChar ψ hψ := by
  subst h
  rfl

variable {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
  [Algebra K M]

theorem charLift_of_isLift (h1 : Module.finrank K M = 1) {a : ℕ} {π : CuspSub K a} {P : CuspSub M a}
    (hP : IsLift π P) : CharLift π P := by
  refine ⟨hP, fun v u _ τ T hτ hT ξ hξ hs => ?_⟩
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  have hO : Over e v u := over_of_liesOver e he v u
  let i := locEquiv hO
  have hi : Continuous i := continuous_cLoc hO
  have hi' : Continuous i.symm := continuous_cLoc hO.symm
  obtain ⟨E, hE⟩ := hP.loc v u i hi (fun x => cLoc_algebraMap hO x) τ T hτ hT
  have hg : ∀ g : GL (Fin a) (u.adicCompletion M),
      GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (τ.ρ.comp (GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) T.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change E (τ.ρ (GeneralLinearGroup.map i.symm.toRingHom g) x) = T.ρ g (E x)
      rw [hE, hg]⟩ E.bijective
  have hs2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hs).of_equiv φ
  have hN := normU_eq e he hO
  have hc : (chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') =
      chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    unfold chars
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    have hj : IsSmoothChar ((ξ j).comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
      have := GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j)
      rwa [hN] at this
    rw [Function.comp_apply, trGL_ofChar i hi' (ξ j) (hξ j) hj]
    exact ofChar_congr (by rw [hN]) _ _
  rw [← hc]
  exact hs2

end Lift

theorem exists_charLift : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a _ π
  obtain ⟨P, hP⟩ := GlobalTheory.DegOneLift.isLift K M h1 a π
  exact ⟨P, charLift_of_isLift h1 hP⟩

end GlobalTheory.DegOneChar
