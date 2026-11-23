import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TransportGL

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem map_map_symm (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g :=
  Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)

theorem det_map (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom g) =
      Units.map i.toRingHom.toMonoidHom (GeneralLinearGroup.det g) := by
  ext
  simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  and_congr Iff.rfl ⟨isCuspidal_of_equiv (equivRep π).symm, isCuspidal_of_equiv (equivRep π)⟩

def transEquiv (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    Representation.Equiv (π.ρ.comp (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) π'.ρ :=
  .mk e fun g => LinearMap.ext fun v => by
    show e (π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) v) = π'.ρ g (e v)
    rw [he, map_map_symm]

theorem symm_rel (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    ∀ g w, e.symm (π'.ρ g w) = π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) (e.symm w) := fun g w => by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply, map_map_symm]

theorem repRel_tw (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (hc : ∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) :
    RepRel i ((cls π).tw χ hχ) ((cls π').tw χ' hχ') := by
  refine ⟨n, irrTwist π _ hχ.detChar, irrTwist π' _ hχ'.detChar, e, congrArg (Sigma.mk n) (clTwist_cl π _ hχ.detChar),
    congrArg (Sigma.mk n) (clTwist_cl π' _ hχ'.detChar), fun g (v : π.V) => ?_⟩
  show e (twist π.ρ (detChar _ χ) g v) = twist π'.ρ (detChar _ χ') (GeneralLinearGroup.map i.toRingHom g) (e v)
  rw [twist_apply, twist_apply, map_smul, he, detChar_apply, detChar_apply, det_map, hc]

end GlobalTheory.LocLanglands.TransportGL

open GlobalTheory.LocLanglands.TransportGL in

theorem GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  have hs := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  refine ⟨fun x x' ⟨n, π, π', e, hx, hx', he⟩ => ?_, fun χ hχ χ' hχ' hc => ?_⟩
  · subst hx hx'
    refine ⟨?_, fun s => repRel_tw i π π' e he _ _ _ _ (hs.2.2.2.2 s)⟩
    rw [isCusp_cls, isCusp_cls]
    refine and_congr Iff.rfl ⟨fun h => isCuspidal_of_equiv (transEquiv i π π' e he)
      (isCuspidal_comp_generalLinearGroupMap i hs.1 _ h), fun h => isCuspidal_of_equiv
      (transEquiv i.symm π' π e.symm (symm_rel i π π' e he)) (isCuspidal_comp_generalLinearGroupMap i.symm hi _ h)⟩
  · refine ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ' hχ', LinearEquiv.refl ℂ ℂ, rfl, rfl, fun g (v : ℂ) => ?_⟩
    show twist (Representation.trivial ℂ (GL (Fin 1) k) ℂ) (detChar (Fin 1) χ) g v =
      twist (Representation.trivial ℂ (GL (Fin 1) k') ℂ) (detChar (Fin 1) χ') (GeneralLinearGroup.map i.toRingHom g) v
    rw [twist_apply, twist_apply, detChar_apply, detChar_apply, TransportGL.det_map, hc]
    rfl

end
