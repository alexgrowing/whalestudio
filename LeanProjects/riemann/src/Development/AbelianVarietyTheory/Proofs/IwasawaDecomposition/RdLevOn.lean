import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCopy
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JoinEquivEqAtReference

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix

namespace GlobalTheory.SeeSaw.TwLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def RatAt (Q : Finset (HeightOneSpectrum (𝓞 E))) : Set (GL (Fin n) (AfE F E)) :=
  {z | ∀ P : Q, ∀ i j, ∃ e : E, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e}

variable [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}

variable (hc : CMData F E) in

def RdLevOn {K : Type} [Field K] (A : Set (GL (Fin n) (AfE F E))) (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ) : Prop :=
  ∀ z ∈ A, ∀ hz : z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    (z ∈ U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) (h' : ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) =
          (∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹) * ∏ P : Q, ((lamQ P ⟨_, h' P⟩ : ℂˣ) : ℂ)

end GlobalTheory.SeeSaw.TwLev
