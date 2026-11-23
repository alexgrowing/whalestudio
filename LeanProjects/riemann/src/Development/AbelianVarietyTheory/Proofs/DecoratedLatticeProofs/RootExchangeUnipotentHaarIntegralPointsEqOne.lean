import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.UnitVolN
open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

theorem mkNel_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c) ↔ ∀ i, e i ∈ 𝒪[k] := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · rintro ⟨h1, -⟩ i
    have := congrFun (co_mkNel (k := k) p e) i
    rw [← this]
    exact h1 _ _
  · intro he
    have hent : ∀ r s, ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val r s ∈ 𝒪[k] := by
      intro r s
      change mkN p e r s ∈ 𝒪[k]
      simp only [mkN, Matrix.of_apply]
      split_ifs with h
      · exact he _
      · rw [Matrix.one_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _
    refine ⟨hent, fun i j => ?_⟩
    set g : GL (n ⊕ Fin c) k := ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) with hg
    have hdet : g.val.det = 1 := det_mkN p e
    have hinv : (g⁻¹).val = g.val.adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet]; simp
    let A : Matrix (n ⊕ Fin c) (n ⊕ Fin c) 𝒪[k] := fun r s => ⟨g.val r s, hent r s⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    rw [hinv, ← hA, ← RingHom.map_adjugate]
    exact (A.adjugate i j).2

end GlobalTheory.HaarR.UnitVolN
end

open GlobalTheory.RootEx.VolN in

theorem GlobalTheory.HaarR.volN_KO_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), IsUnitVol ν → volN ν n c p {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = 1 := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [volN_eq, MeasurableEquiv.map_apply]
  have : (coEquiv (k := k) (n := n) (c := c) p) ⁻¹' {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} =
      Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
    exact GlobalTheory.HaarR.UnitVolN.mkNel_mem_KO_iff p e
  rw [this, Measure.pi_pi]
  simp [hν.2]
