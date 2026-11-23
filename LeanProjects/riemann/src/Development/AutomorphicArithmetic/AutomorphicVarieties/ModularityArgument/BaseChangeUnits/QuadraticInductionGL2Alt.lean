import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Published UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IndSys (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (satP : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 F)) (B + B')) ∧
    (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧
      B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 F)) B)

end Sys

def IndCh {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (e : Γ' →* Γ) (r : Γ' →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k) : Prop :=
  ∀ t : Γ, t ∉ e.range →
    (∀ g g' : Γ', e g' = t⁻¹ * e g * t → (R (e g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (r g : Matrix (Fin 2) (Fin 2) k).charpoly * (r g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
    ∀ g : Γ', e g = t * t →
      (R t : Matrix (Fin 4) (Fin 4) k).charpoly = (r g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

def IndFin (P : TR.CuspSub ℚ (2 * 2)) (π : TR.CuspSub E 2) : Prop := IndSys π.HasSat P.HasSat

def MixWt (π : TR.CuspSub E 2) : Prop :=
  ∃ (m m' : Fin 2 → ℤ) (v v' : InfinitePlace E), v ≠ v' ∧ π.HasInfChar v (infOf m) ∧ π.HasInfChar v' (infOf m') ∧
    Function.Injective ![m 0, m 1, m' 0, m' 1]

def CentQ (π : TR.CuspSub E 2) : Prop :=
  ∃ ω : HChar ℚ, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ω.UnrAt (w.under (𝓞 ℚ)) ∧ ∀ f : ℕ,
    normV w = normV (w.under (𝓞 ℚ)) ^ f → ∃ B, π.HasSat w B ∧ B.prod = ω.val (w.under (𝓞 ℚ)) ^ f

end Defs

def IndWeakQ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E], Module.finrank ℚ E = 2 → ∀ π : TR.CuspSub E 2, MixWt π →
    ∃ P : TR.CuspSub ℚ (2 * 2), IndFin P π

def IndWeakQd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E], Module.finrank ℚ E = 2 → ∀ π : TR.CuspSub E 2, MixWt π → CentQ π →
    ∃ P : TR.CuspSub ℚ (2 * 2), IndFin P π

theorem IndWeakQ.d (h : IndWeakQ) : IndWeakQd := fun E _ _ _ h2 π hm _ => h E h2 π hm

def InfOfL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E], Module.finrank ℚ E = 2 →
    ∀ (P : TR.CuspSub ℚ (2 * 2)) (π : TR.CuspSub E 2), IndFin P π →
    ∀ (v v' : InfinitePlace E) (u : InfinitePlace ℚ) (m m' M : Multiset ℂ), v ≠ v' → π.HasInfChar v m → π.HasInfChar v' m' →
      P.HasInfChar u M → M = m + m'

def InfOfLU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E], Module.finrank ℚ E = 2 →
    ∀ (P : TR.CuspSub ℚ (2 * 2)) (π : TR.CuspSub E 2), Lit.IsUnitaryR P → Lit.IsUnitaryR π → IndFin P π →
    ∀ (v v' : InfinitePlace E) (u : InfinitePlace ℚ) (m m' M : Multiset ℂ), v ≠ v' → π.HasInfChar v m → π.HasInfChar v' m' →
      P.HasInfChar u M → M = m + m'

def QuadraticInductionGL2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E], Module.finrank ℚ E = 2 → ∀ π : TR.CuspSub E 2, MixWt π → CentQ π →
    ∃ P : TR.CuspSub ℚ (2 * 2), IndFin P π ∧ ∀ (v v' : InfinitePlace E) (u : InfinitePlace ℚ) (m m' : Multiset ℂ), v ≠ v' →
      π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar u (m + m')

def IndAutL : Prop := S2.AllInd fun T ι R _ => IsAutC ι (R.comp (resQ T.L))

def MixWtC (K : Type) [Field K] {M : Type} [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M] (π : CuspSub M 2) : Prop :=
  ∀ φ : K →+* ℂ, ∃ (m m' : Fin 2 → ℤ) (τ τ' : M →+* ℂ), τ ≠ τ' ∧ τ.comp (algebraMap K M) = φ ∧ τ'.comp (algebraMap K M) = φ ∧
    π.HasInfChar τ (infOf m) ∧ π.HasInfChar τ' (infOf m') ∧ Function.Injective ![m 0, m 1, m' 0, m' 1]

def IndC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, MixWtC K π →
    ∃ P : CuspSub K (2 * 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat ∧ ∀ (τ τ' : M →+* ℂ) (m m' : Multiset ℂ), τ ≠ τ' →
      τ.comp (algebraMap K M) = τ'.comp (algebraMap K M) → π.HasInfChar τ m → π.HasInfChar τ' m' →
      P.HasInfChar (τ.comp (algebraMap K M)) (m + m')

def IndAutC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → MixWtC K π →
    ∀ R : G K Ω →* GL (Fin 4) (Qbar l), IsSSRep R → IndCh (galEmb K M Ω) r R → IsAutC ι R

def UpQuadI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub F 2), Continuous r → π.IsRegAlg → AttR ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m

def UpSolI : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub F 2), Continuous r → (CG.mk π).IsRegAlg → AttC ι r π →
      IsIrr (r.comp (galEmb F E Ω)) → ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
        ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m

def AttInd : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin 2) (Qbar l)) (R : G F Ω →* GL (Fin 4) (Qbar l)) sat satP, (∀ w B B', sat w B → sat w B' → B = B') →
    (∀ w B B', satP w B → satP w B' → B = B') → AttachedSys ι r sat → IndSys (F := F) (E := E) sat satP → IsSSRep R →
    IndCh (galEmb F E Ω) r R → AttachedSys ι (tw R (cycBar F Ω l)⁻¹) satP

end UpperTheory.V.Z.Bc

end
