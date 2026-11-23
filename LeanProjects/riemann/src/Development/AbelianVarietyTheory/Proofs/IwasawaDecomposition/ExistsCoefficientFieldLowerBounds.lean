import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.CoeffFieldLower

theorem finiteDimensional_muK_one (l : ℕ) [Fact l.Prime] : FiniteDimensional ℚ_[l] (muK l 1) := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have hfin : ({x : PadicAlgCl l | x ^ (l ^ 1) = 1}).Finite :=
    (nthRoots (l ^ 1) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]; exact hx
  have := hfin.to_subtype
  show FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | x ^ (l ^ 1) = 1})
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

open Classical in

def bridgeLow (D : D7) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)) : Loc.FinExt l :=
  if hw : w ∈ placesOver D.host.E l then
    (Classical.choose_spec (GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w))).choose
  else ⟨⊥, inferInstance⟩

def low (D : D7) : Big D := fun l hl j =>
  haveI := hl
  ⟨IntermediateField.adjoin ℚ_[l] (Set.range j) ⊔ muK l 1 ⊔
      ⨆ w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset, (bridgeLow D l w).1, by
    have := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range j
    have := finiteDimensional_muK_one l
    have : ∀ w, FiniteDimensional ℚ_[l] (bridgeLow D l w).1 := fun w => (bridgeLow D l w).2
    infer_instance⟩

theorem exists_low : ∀ (D : D7), ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l), (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧ ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l, ∃ Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0), ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 := by
  intro D
  refine ⟨low D, fun l _ j => ⟨fun x => ?_, ?_, fun K0 hK0 w hw => ?_⟩⟩
  · have h1 : IntermediateField.adjoin ℚ_[l] (Set.range j) ≤ (low D l j).1 := le_sup_left.trans le_sup_left
    exact h1 (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact le_sup_right.trans le_sup_left
  · have hex := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
    have hspec := (Classical.choose_spec hex).choose_spec
    have hL : (bridgeLow D l w).1 ≤ K0.1 := by
      refine le_trans ?_ hK0
      refine le_trans ?_ le_sup_right
      have hmem : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset := by simpa using hw
      exact le_iSup₂ (f := fun w (_ : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset) =>
        (bridgeLow D l w).1) w hmem
    have e : bridgeLow D l w = (Classical.choose_spec hex).choose := dif_pos hw
    have hL' : (Classical.choose_spec hex).choose.1 ≤ K0.1 := e ▸ hL
    obtain ⟨Bw, hBj, -⟩ := hspec.2 K0 hL'
    exact ⟨Bw, fun x => by rw [hBj]; exact hspec.1 x⟩

end GlobalTheory.CoeffFieldLower

end
