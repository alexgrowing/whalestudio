import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneUniformInLevelStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.OneComb

theorem exists_open_fix' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), IsCO L.J → ∀ α, ∃ e, IsOneComb ψ ν P L α e := by
  intro k _ _ _ _ _ _ n _ _ c P h1 hP ψ hψc hψ1 ν hν L hL α
  obtain ⟨U, hU, h⟩ := exists_open_fix' L hL.1 α
  obtain ⟨e, e', he⟩ := GlobalTheory.T.exchangeToPositionOne_uniform_in_level k n c P h1 hP ψ hψc hψ1 ν hν U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

end GlobalTheory.QPl.OneComb
