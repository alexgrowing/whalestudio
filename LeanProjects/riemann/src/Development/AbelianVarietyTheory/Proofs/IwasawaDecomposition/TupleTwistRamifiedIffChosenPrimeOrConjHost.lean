import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dif_pos hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
