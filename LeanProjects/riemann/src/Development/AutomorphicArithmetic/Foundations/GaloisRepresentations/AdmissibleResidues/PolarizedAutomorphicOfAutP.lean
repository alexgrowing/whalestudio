import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base
open private ss_conj from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
open private isIrr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible
open private charpoly_conj_gl from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem Wit.iso' [IsCMField F] (e : RepIso r r') (hU : Wit ι r) : Wit ι r' := by
  intro w hw A hA hfin
  obtain ⟨g, hg⟩ := e
  have hfin' : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (hfin.image (fun x => g⁻¹ * x * g)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨r' s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [hg s]
    group
  obtain ⟨s, j, hj, hF, h⟩ := hU w hw A hA hfin'
  refine ⟨s, j, hj, hF, fun α β hα hβ k hk => ?_⟩
  rw [hg s, charpoly_conj_gl] at hα hβ
  exact h α β hα hβ k hk

theorem attC_iso [IsTotallyComplex F] {π : CuspSub F n} (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π :=
  ⟨ss_conj h.choose h.choose_spec H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : IsAutCsdN ι r) : IsAutCsdN ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).iso' h⟩

def AutPN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := AutPol ι r ∧ Wit ι r
end

def AutQIsoN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → IsAutQN ι r' → IsAutQN ι r

def NewformAut0 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutomorphicOverImagQuad ι W

def Up30 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 3) (Qbar l)),
    IsAutR ι r → IsAutomorphicOverImagQuad ι r

end UpperTheory.GalN.V
