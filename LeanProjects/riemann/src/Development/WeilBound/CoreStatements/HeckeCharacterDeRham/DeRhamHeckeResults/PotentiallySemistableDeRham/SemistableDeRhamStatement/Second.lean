import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.BdRAlg

noncomputable section

namespace DeRhamPotentiallySemistable.DRPst

open Formalism.Per6 GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def qQ : ℚ_[l] →+* BdR l := (algebraMap (BdRp l) (BdR l)).comp (algebraMap ℚ_[l] (BdRp l))

def iC : ACris.ACris ℂ_[l] l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (ACris.iota ℂ_[l] l)

def tQ : BdR l := iC l (tA l)

def uQ : BdR l := algebraMap (BdRp l) (BdR l) (uBdR l)

def Bst : Subring (BdR l) :=
  Subring.closure (Set.range (iC l) ∪ {((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l})

variable {l}

def IsAdm (S : Set (BdR l)) {d : ℕ} (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l))
    (r : G → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
    ∀ σ : G, (r σ).map (qQ l) * P.map (σD σ.1) = P

theorem fix_mono {K L : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : K ≤ L)
    (σ : L.fixingSubgroup) : σ.1 ∈ K.fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone h σ.2

end DeRhamPotentiallySemistable.DRPst

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst in

def DeRhamPotentiallySemistable.DeRhamPotSemistable2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (d : ℕ) (ρ : K.fixingSubgroup →* GL (Fin d) ℚ_[l]),
    Continuous (fun σ => (ρ σ : Matrix (Fin d) (Fin d) ℚ_[l])) →
    IsAdm Set.univ K.fixingSubgroup (fun σ => (ρ σ : Matrix (Fin d) (Fin d) ℚ_[l])) →
    ∃ (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (h : K ≤ L), FiniteDimensional ℚ_[l] L ∧
      IsAdm (Bst l : Set (BdR l)) L.fixingSubgroup
        (fun σ => (ρ ⟨σ.1, fix_mono h σ⟩ : Matrix (Fin d) (Fin d) ℚ_[l]))
