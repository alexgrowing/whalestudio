import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleRankThreeStrengthen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.IsRootCharpolySmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyRootPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wdown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wread
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private isIrr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem AutCsd0.pol [IsCMField F] (h : AutCsd0 ι r) : AutPol ι r := by
  obtain ⟨π, hreg, hd, ha⟩ := h
  refine ⟨π, hreg, ⟨quadChar F ^ n, fun v => ?_, ?_⟩, ha⟩
  · have e : (quadChar F ^ n).locInf v (-1) = (quadChar F).locInf v (-1) ^ n := rfl
    rw [e, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow]
    exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd

def IsRegAlgAutomorphicAttached [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π

theorem AutCsd0.c0 [IsCMField F] (h : AutCsd0 ι r) : IsRegAlgAutomorphicAttached ι r := h.imp fun _ k => ⟨k.1, k.2.2⟩
theorem AutPol.c0 [IsCMField F] (h : AutPol ι r) : IsRegAlgAutomorphicAttached ι r := h.imp fun _ k => ⟨k.1, k.2.2⟩

variable [IsAlgClosure F Ω]

theorem Wit.iso [IsCMField F] (e : RepIso r r') (h : Wit ι r) : Wit ι r' := L.wiso F Ω l n r r' e h

theorem Wit.tw [IsCMField F] (_P : Hypotheses₂) {μ : G F Ω →* (Qbar l)ˣ} (_hμ : IsAlgChar ι μ) (hc : Continuous μ) (_ha : IsRegAlgAutomorphicAttached ι r)
    (h : Wit ι r) : Wit ι (Af.tw r μ) := L.wtw F Ω l n r μ hc h

section
variable (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem Wit.up (_P : Hypotheses₂) [IsGalois F K] (_hs : Group.IsSolvable (K ≃ₐ[F] K)) (_hc : Continuous r) (_ha : IsRegAlgAutomorphicAttached ι r)
    (_hb : IsRegAlgAutomorphicAttached ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (h : Wit ι r) :
    Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := L.wup F Ω l n r K h

theorem Wit.down (_P : Hypotheses₂) [IsGalois F K] (_hs : Group.IsSolvable (K ≃ₐ[F] K)) (_hc : Continuous r) (_ha : IsRegAlgAutomorphicAttached ι r)
    (_hb : IsRegAlgAutomorphicAttached ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)))
    (h : Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) : Wit ι r := L.wdown F Ω l n r K h
end

theorem WitQ.iso (e : RepIso r r') (h : WitQ ι r) : WitQ ι r' := by
  intro K _ _ _ _ _ _ h2 hi
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed F, haveI := IsAlgClosure.isAlgebraic (R := F) (K := Ω); Algebra.IsAlgebraic.tower_top (K := F) K⟩
  obtain ⟨g, hg⟩ := e
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    ⟨g, fun s => hg _⟩
  exact (h K h2 (isIrr_iso e'.symm' hi)).iso e'

theorem Wit.read [IsCMField F] (_P : Hypotheses₂) {π : CuspSub F n} (_hreg : (CG.mk π).IsRegAlg) (_hatt : AttC ι r π) (hc : Continuous r)
    (hW : Wit ι r) {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (hf : (r '' (Ine (F := F) A : Set (G F Ω))).Finite) {rc : IrrGL (w.adicCompletion F) → WD h} (_hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (_hσ : π.IsLocComp w σ) (k : WDN ι r (rc (algNorm σ))) :
    IsWDOf ι r (rc (algNorm σ)) :=
  L.wread F Ω l n r ι w A h hl _ hc hW hf (k.awV hl).pol (k.awV hl).n0

omit [IsAlgClosure F Ω] in
theorem Wit.born [IsCMField F] (h : Unlinked r) : Wit ι r := h

theorem IsAutCsdN.iso [IsCMField F] (e : RepIso r r') (h0 : AutCsd0 ι r') (h : IsAutCsdN ι r) :
    IsAutCsdN ι r' := ⟨h0, fun c => (h.2 (continuous_of_iso c e.symm')).iso e⟩

end UpperTheory.GalN.V
