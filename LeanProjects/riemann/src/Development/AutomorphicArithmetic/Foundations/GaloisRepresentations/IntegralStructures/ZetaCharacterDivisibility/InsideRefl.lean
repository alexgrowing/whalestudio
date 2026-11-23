import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DivisionOfDeterminantCharacter
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.RowDefOfOdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.StGalW

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Div

section Alg

variable {Γ k : Type} [Group Γ] [Field k] {a d : ℕ}

def Inside (r : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin d) k) : Prop :=
  ∃ A : Matrix (Fin d) (Fin a) k, A.rank = a ∧ ∀ g : Γ, (ρ g : Matrix (Fin d) (Fin d) k) * A = A * (r g : Matrix (Fin a) (Fin a) k)

def Covers (r : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin d) k) : Prop :=
  ∃ (m : ℕ) (B : Matrix (Fin a × Fin m) (Fin d) k), B.rank = d ∧
    ∀ g : Γ, Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * B = B * (ρ g : Matrix (Fin d) (Fin d) k)

theorem inside_refl (r : Γ →* GL (Fin a) k) : Inside r r := ⟨1, by simp, fun g => by simp⟩

end Alg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a dd : ℕ}

def CrysAt (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
    IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

def PhiPol (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
    ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g

def PhiKilled (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
    IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧ ∃ g : Weil h, deg g = -1 ∧ ∃ m : ℕ,
      (wdAt P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype)).charPol g ∣ ((GlobalTheory.RoadU.satWD h a B).charPol g) ^ m

def HTRichEx (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (a : ℕ) : Prop :=
  ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ IsPlaceOver A w ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
      (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw ∧
    ∃ (τ : E →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J ∧
      ∃ J₀ : Finset ℤ, J₀.card = a ∧ (∀ j ∈ J₀, j ∈ J) ∧ Lacunary J₀

variable [IsCMField E]

def JumpsOcc (U : Submodule ℂ (UA E a → ℂ)) (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin dd) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∀ (lam : DomWeight a) (J : Multiset ℤ), HasWeightAt U (ι.toRingHom.comp τ) lam →
          J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          ∃ J' : Multiset ℤ, IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J' ∧ ∀ j ∈ J, j ∈ J'

def VBase (ι : Qbar l ≃+* ℂ) (d : ℕ) (U : Submodule ℂ (UA E a → ℂ))
    (ρ : G E Ω →* GL (Fin dd) (Qbar l)) : Prop :=
  Continuous ρ ∧ IsSSRep ρ ∧
    (∃ X : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
      ∀ B : Multiset ℂˣ, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧ HTRichEx ρ a

def IsDetChar (ι : Qbar l ≃+* ℂ) (U : Submodule ℂ (UA E a → ℂ)) (ψ : G E Ω →* (Qbar l)ˣ) : Prop :=
  Continuous ψ ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ B : Multiset ℂˣ, SatU U w B →
    ∃ J : (E →+* Qbar l) → Multiset ℤ, Cl ι (rk1 ψ) w {(algSat a (normV w) B).prod} J

def IsDivRep (ι : Qbar l ≃+* ℂ) (d : ℕ) (U : Submodule ℂ (UA E a → ℂ))
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧
    ∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
      ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ B, SatU U w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
          (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
            ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
              ((algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod

def GenM : ℕ → ℕ → Multiset ℂˣ → Prop := fun _ _ B => GenericMul B

def PhiSeed : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a dd : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)) (ψ : G E Ω →* (Qbar l)ˣ), IsDetChar ι U ψ →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsSSRep ρ → Inside r ρ →
    (∀ g, (r g : Matrix (Fin a) (Fin a) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ B : Multiset ℂˣ, SatU U w B → GenericMul B → PhiKilled ι ρ w a B →
      CrysAt r w ∧ PhiPol ι r w B

def DetEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∃ ψ : G E Ω →* (Qbar l)ˣ, IsDetChar ι U ψ

def DivAll : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ d : ℕ, ImQ E d → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U →
    (∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), IsDivRep ι d U r ∧
      ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ → ∀ w : HeightOneSpectrum (𝓞 E),
        (IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → GenericMul B → ESAt ι ρ w (algSat a (normV w) B) →
          FrobEig ι r w (algSat a (normV w) B)) ∧
        (CrysAt ρ w → JumpsOcc U ι ρ w → CrysDRU U ι r w) ∧
        (IsSplitAt w → ∀ B, SatU U w B → GenericMul B → PhiKilled ι ρ w a B → CrysAt r w ∧ PhiPol ι r w B)

def PhiOfDiv : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ d : ℕ, ImQ E d → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), IsDivRep ι d U r →
    ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsSSRep ρ → Inside r ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ B, SatU U w B → GenericMul B → PhiKilled ι ρ w a B →
      CrysAt r w ∧ PhiPol ι r w B

theorem PhiPol.phiAt {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : PhiPol ι r w B) : PhiAt ι r w B := by
  intro P AI hT A hA O _ _ _ Bw hj σ n
  unfold GlobalTheory.CongPhi.phiSum
  rw [h P AI hT A hA O Bw hj σ]

end UpperTheory.Gal.Int.Div

end
