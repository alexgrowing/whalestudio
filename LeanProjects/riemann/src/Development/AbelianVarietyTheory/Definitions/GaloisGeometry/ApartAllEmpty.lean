import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def AutomorphicTypeClass : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), HeightOneSpectrum (𝓞 E) → CuspSub E a → Prop

def ImQ (E : Type) [Field E] (d : ℕ) : Prop :=
  0 < d ∧ ∃ x : E, x ^ 2 = -(d : E)

def SqAt (d q : ℕ) [Fact q.Prime] : Prop :=
  IsSquare (-(d : ℚ_[q]))

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def UsPl (d : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  IsSplitAt w ∧ ∀ (q : ℕ) (hq : q.Prime), ((q : ℕ) : 𝓞 E) ∈ w.asIdeal → @SqAt d q ⟨hq⟩

def ApartAll (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u ∈ S, Apart w u

def SphOff (w₀ : HeightOneSpectrum (𝓞 E)) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → ApartAll S w → ∃ B, (CG.mk π).HasSat w B

def GenAt (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ B, (CG.mk π).HasSat w B → Gen a (normV w) B

def SeedW (Ty : AutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ π' : CuspSub E a, ScopeOffT l T π' → Ty E l a w₀ π' → SphOff w₀ S π' → (∀ z ∈ Z₀, GenAt Gen π' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (U : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen U ∧ Dense U ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Apart w w₀ → ApartAll S w →
            ∀ B, (CG.mk π').HasSat w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ U →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Apart w w₀ → ApartAll S w →
          ∀ B, (CG.mk π').HasSat w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → ApartAll S w →
          ClauseAt .crys π' ι r w ∧ ClauseAt .dR π' ι r w)

structure NbrW (l : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a)
    (π π' : CuspSub E a) : Prop where
  scope : ScopeOffT l T π'
  inf : ∀ τ, (CG.mk π').infChar τ = (CG.mk π).infChar τ
  level : HasLevel w₀ Kw π'

def CongGLW (Ty : AutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ (T : Finset (HeightOneSpectrum (𝓞 E))) (Kw : Levels E a), NonSplitSet T ∧ Adapted w₀ Kw π ∧
      ∀ Z : Finset (HeightOneSpectrum (𝓞 E)),
        (∀ z ∈ Z, IsSplitAt z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ∃ B, (CG.mk π).HasSat z B) →
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), O.IsSys π θ →
        PolyApprox θ {θ' | ∃ π', NbrW l T w₀ Kw π π' ∧ Ty E l a w₀ π' ∧ (∀ z ∈ Z, GenAt Gen π' z) ∧ O.IsSys π' θ'} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def LimW : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, ImQ E d → SqAt d l →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → (∃ B, (CG.mk π).HasSat w B) →
        ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w)

theorem apartAll_empty (w : HeightOneSpectrum (𝓞 E)) : ApartAll (∅ : Finset (HeightOneSpectrum (𝓞 E))) w :=
  fun _ h => absurd h (Finset.notMem_empty _)

example : ¬ ImQ ℚ 1 := fun ⟨_, x, hx⟩ => by
  have h := sq_nonneg x
  push_cast at hx
  linarith

end GlobalTheory.CongL

end
