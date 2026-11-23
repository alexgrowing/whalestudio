import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def HasDiv {n : ℕ} (O : Subring L) (d : List ℤ) (g : GL (Fin n) L) : Prop :=
  ∃ ϖ : L, Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      (g : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) L)

def divInd {n : ℕ} (O : Subring L) (d : List ℤ) : GL (Fin n) L → ℂ := Set.indicator {g | HasDiv O d g} 1

def bcPar (n : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) + Multiset.replicate (n % 2) 1

def ParU (σ : L →+* L) (q n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (0 : ℂ) ∉ s ∧ (∃ α, bcPar n α = s) ∧ ∀ α : Fin (n / 2) → ℂ, bcPar n α = s →
    ∀ φ : GU σ n → ℂ, IsSphericalU q α φ → ∀ d, lab d →
      hAct (KU σ n) (fun g : GU σ n => divInd (intL L) d (g : GL (Fin n) L)) φ 1 = c d * φ 1

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

def ParGL (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  s.card = n ∧ (0 : ℂ) ∉ s ∧ ∀ α : Fin n → ℂ, Finset.univ.val.map α = s →
    ∀ φ : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P α φ → ∀ d, lab d →
      hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 = c d * φ 1

variable [StarRing E]

def IsConjAt (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E) : Prop :=
  ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (star x)

def IsPar (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal ≠ P.asIdeal → ParGL P n lab c s) ∧
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal →
    ∀ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E) (q : ℕ),
      IsConjAt P σ → IsUnramInv ϖ σ q → ParU σ q n lab c s)

end Global

def frobPoly (q n : ℕ) (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun a => X - C (a * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ))).prod

variable {D : D7}

def Lab (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) : Prop :=
  ∃ R, Hecke₂ V J χ S P d R

def HasGalois (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ),
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E (AlgebraicClosure D.host.E) →* GL (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l), Continuous ρ ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D S P → ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
        ∃ s, IsPar P V.rank (Lab V J χ S P) (c P) s ∧
          ∀ (A : ValuationSubring (AlgebraicClosure D.host.E)) (g : Formalism.ConjugateSelfDual.G D.host.E (AlgebraicClosure D.host.E)),
            Formalism.ConjugateSelfDual.IsPlaceOver (F := D.host.E) A P → Formalism.ConjugateSelfDual.IsFrob (F := D.host.E) A (Formalism.ConjugateSelfDual.normV P) g →
              ((ρ g⁻¹ : GL (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
                (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = frobPoly (Formalism.ConjugateSelfDual.normV P) V.rank s

def RegularWt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ (a b : Fin V.rank), a < b → M.lam τ b + 2 ≤ M.lam τ a

def GaloisOfRegularForms : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    IsInfFam θ → RegularWt M → SphOff J χ Sb → partFull θ M J χ Sb c ≠ ⊥ → HasGalois V J χ Sb c

theorem bcPar_map_inv (n : ℕ) (α : Fin (n / 2) → ℂ) : (bcPar n α).map (·⁻¹) = bcPar n α := by
  simp only [bcPar, Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map (fun i => (α i)⁻¹) _)]

end GlobalTheory.SphPar

end
