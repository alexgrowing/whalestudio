import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOffS0LastLevelIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointCarriesLatticeToMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowShape

theorem moves_of_forall {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L)
    (hM : Submodule.IsLattice D.host.E M) (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L M (· = v)) :
    GlobalTheory.FinPl.Moves S g L M (fun _ => True) := by
  intro y hy
  have hT := fun (N : GlobalTheory.FinPl.Lat S) (hN : Submodule.IsLattice D.host.E N) (z : Fin S.rank → AE D) =>
    ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 N z hN
  have hmy : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [hT L hL y, hT M hM _]
  refine ⟨fun ⟨_, h2⟩ => ⟨hmy, fun v _ e he => ?_⟩, fun ⟨_, h2⟩ => ⟨hy, fun v _ e he => ?_⟩⟩
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    have := (h v (e • y) hs).1 (h2 v trivial e he)
    rwa [Matrix.mulVec_smul] at this
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    refine (h v (e • y) hs).2 ?_
    rw [Matrix.mulVec_smul]
    exact h2 v trivial e he

theorem moves0_of_selfDual : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G 0) → ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hN t b hb
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc := hch.guard t
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hΛ : IsSelfDualC _ (ch.G.Λ (.grid D.R.m 0)) :=
    (ch.G.isV (X := .grid D.R.m 0) ⟨le_rfl, Nat.zero_le _⟩ (fun j e => by injection e with h1 h2; omega)).sd
  apply moves_of_forall _ _ _ _ hΛ.1 hN.1
  intro v
  classical
  by_cases hv : ∃ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) = v
  · obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨e, ⟨⟨es, hes, -⟩, -⟩, -, -⟩ := hb.1
    obtain ⟨p, hpe, hpv, hpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w (es w) (hes w hw) s.hF
    have key := GlobalTheory.T.gridBasePoint_carries_lattice_to_movedLattice hL hde ch.G ch.W Set.univ ch.S.toGridChoice t trivial hc b hb w hw p (hpe ▸ hes w hw) hpr
    rw [← hpv, ← GlobalTheory.Core.Mi.LatMatch.sMoves_one]
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D _ p _ _ _ 1 (b 0) hΛ hN (GlobalTheory.Core.Mi.LatMatch.normOneAt_one _) fun x => ?_
    rw [map_one, one_smul]
    exact key x
  · push_neg at hv
    have hv0 : v ∉ ch.G.pl.S0 := fun h0 => hv (ch.G.pl.w v)
      (Finset.mem_union_left _ (by simpa [Places.W0] using ⟨v, h0, rfl⟩)) (ch.G.pl.under_w h0)
    intro y hy
    rw [GlobalTheory.T.gridBasePoint_trivial_offTensorPlaces ch.G t ch.S.B b hb v hv y hy]
    exact GlobalTheory.T.lattice_off_S0_last_level_iff ch.G v hv0 y hy

theorem moves0 : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True :=
  big_mono (fun _ h => h.1 (h.2 0 (Nat.zero_le _))) (Big.and moves0_of_selfDual GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth)

end GlobalTheory.RowShape
