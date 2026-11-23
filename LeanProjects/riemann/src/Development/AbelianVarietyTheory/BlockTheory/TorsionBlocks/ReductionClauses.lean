import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Clauses

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def DepthZero {w : PlE H} (L : A.LP w) : Prop :=
  ∀ σ ∈ wildSet N (N.plOm.1 w), A.inePol L σ = (X - 1) ^ A.lpDim L

def Hyp (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)) : Prop :=
  ((∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r) ∧
  HasParamX N A i x Sig ∧
  (∀ k, ∀ w ∈ placesOver H.E (H.g k), DepthZero N A (isoLoc N A Sig w)) ∧
  goodSig N A Sig

def ClauseA (Sig : List (Part A.CG)) : Prop :=
  ∃ π : A.CG R.r, Sig = [⟨R.r, π, 1⟩] ∧ A.csd π ∧ A.ralg π

def redBar (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    G H.E N.Om →* GL (Fin R.r) (Formalism.CyclotomicNorms.Fbar (N.l i)) :=
  mapRep ((A.kFbar i).comp (IsLocalRing.residue (N.O i))) ρ

def ClauseB (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Formalism.CyclotomicNorms.IrredOn (redBar N A i ρ) ⊤

def ClauseC (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ L : IntermediateField H.E N.Om, FiniteDimensional H.E L → IsGalois H.E L →
    Group.IsSolvable (L ≃ₐ[H.E] L) →
    ∀ k : Fin 2, N.l i ∉ Formalism.CyclotomicNorms.BB R.r (H.g k) →
      (∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om, IsPlaceOver (F := H.E) B w →
        Ine (F := H.E) B ≤ L.fixingSubgroup) →
      Formalism.CyclotomicNorms.IrredOn (redBar N A i ρ) L.fixingSubgroup

variable {A} in

def rootQ (T : NTypes A) (i : N.Loc) (k : Fin 2) (u : (ZMod (H.g k))ˣ) : Qbar (N.l i) :=
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  (A.iotaQC i).symm (T.teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k)) (u : ZMod (H.g k))))

def NoEigCongr (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (γ : G H.E N.Om)
    (z : Qbar (N.l i)) : Prop :=
  ∀ α : Qbar (N.l i),
    ((mapRep (iotaOQ N A i) ρ γ : GL (Fin R.r) (Qbar (N.l i))) :
      Matrix (Fin R.r) (Fin R.r) (Qbar (N.l i))).charpoly.IsRoot α → ¬ ‖α - z‖ < 1

variable {A} in

def ClauseD (T : NTypes A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ (v : N.PlG k) (γ : G H.E N.Om),
    (γ = T.tg k v ∨ ∃ c : N.Om ≃+* N.Om, IsCMConjOm H.E N.Om c ∧
      ∀ y, γ y = c (T.tg k v (c.symm y))) →
    ∀ j' : Fin R.m,
      NoEigCongr N A i ρ γ (rootQ N T i k (N.chiT k v j')) ∧
      NoEigCongr N A i ρ γ (rootQ N T i k (N.chiT k v j')⁻¹)

def ClauseTame (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om,
    IsPlaceOver (F := H.E) B w → ∀ γ : G H.E N.Om, TameGenAt B γ →
      ¬ ((redRep N i ρ γ : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
          Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
        (IsLocalRing.residue (N.O i) ((N.chi i 1 γ : (N.O i)ˣ) : N.O i)) ∧
      ¬ ((redRep N i ρ γ : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
          Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
        (IsLocalRing.residue (N.O i) (((N.chi i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i))

variable {A} in

def RepClauses (T : NTypes A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ClauseB N A i ρ ∧ ClauseC N A i ρ ∧ ClauseD N T i ρ ∧ ClauseTame N i ρ

theorem ClauseA.cusp {Sig : List (Part A.CG)} (h : ClauseA N A Sig) : IsCuspIso N A Sig :=
  let ⟨π, h1, _⟩ := h; ⟨π, h1⟩

end Clauses

def PointIrreducibility (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), Hyp D.nd D.naut i x Sig →
    ClauseA D.nd D.naut Sig ∧
    ∀ (i' : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i')),
      IsRepOfSig D.nd D.naut i' Sig ρ → RepClauses D.nd D.ntypes i' ρ

end GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses

end
