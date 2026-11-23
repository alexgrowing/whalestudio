import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 TensorProduct

section Restrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def genPt (F : Type*) [Field F] (Q : Ideal (MRingOver F ι)) :
    (Σ k, ι k) → FractionRing (MRingOver F ι ⧸ Q) :=
  fun p => algebraMap (MRingOver F ι ⧸ Q) _ (Ideal.Quotient.mk Q (X p))

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]

def IsLocFrac (Q : Ideal (MRingOver (kap O) ι)) (F G : MRingOver O ι) : Prop :=
  ∃ α : K → ℕ, IsMultiHomog F α ∧ IsMultiHomog G α ∧ MvPolynomial.map (IsLocalRing.residue O) G ∉ Q

def stalk (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ s, mseg (genPt (kap O) Q) s ≠ 0 ∧
    ∃ e ∈ B.lat s, v = (aeval x F / aeval x G) • e}

def resRel (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :
    Set (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) :=
  {t | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ m m' : stalk O x Q B,
    (m' : V) = (aeval x F / aeval x G) • (m : V) ∧
    t = (aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) F) /
        aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) G)) ⊗ₜ m - 1 ⊗ₜ m'}

abbrev resFibre (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :=
  (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) ⧸
    Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B)

def resMap (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : stalk O x Q B →+ resFibre O x Q B :=
  (Submodule.mkQ _).toAddMonoidHom.comp
    (TensorProduct.mk ℤ (FractionRing (MRingOver (kap O) ι ⧸ Q)) (stalk O x Q B) 1).toAddMonoidHom

def resLat (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (s : ∀ k, ι k) : AddSubgroup (resFibre O x Q B) :=
  ((B.lat s).addSubgroupOf (stalk O x Q B)).map (resMap O x Q B)

def resSub (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (W : Submodule Ω V) :
    Submodule (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resFibre O x Q B) :=
  Submodule.span _ (resMap O x Q B '' {m | (m : V) ∈ W})

end Restrict

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle MRingOver)

def FullFlagRestriction.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ)
    (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (Q : Ideal (MRingOver (IsLocalRing.ResidueField O) ι)) [Q.IsPrime], ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) ≤ Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) = Q ∧
      ∃ B' : ChartBundle (IsLocalRing.ResidueField O)
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q)) N
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resFibre O x Q B),
        B'.lat = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resLat O x Q B ∧
        ∀ fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B,
          ∃ fl' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag (IsLocalRing.ResidueField O)
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) B',
            fl'.deg = fl.deg ∧ ∀ i, fl'.Vs i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resSub O x Q B (fl.Vs i)

end GroundTheory.Heights₂.Heights.NumbersDVR
