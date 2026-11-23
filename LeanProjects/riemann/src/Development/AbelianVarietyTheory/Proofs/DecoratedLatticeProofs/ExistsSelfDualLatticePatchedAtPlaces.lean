import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.Patch

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_eq_zero_of_ne {x w : Pl D} (h : w ≠ x) {a b : AE D} (ha : a ∈ idAt D (· = x)) (hb : b ∈ idAt D (· = w)) :
    a * b = 0 := by
  apply eq_zero_of_comp
  · rw [map_mul, infPart_of_idAt ha, zero_mul]
  · intro v
    rw [map_mul]
    by_cases hv : v = x
    · rw [compAt_of_idAt hb (w := v) (fun h' => h (h'.symm.trans hv)), mul_zero]
    · rw [compAt_of_idAt ha (w := v) hv, zero_mul]

theorem mulVec_eq_of_ne {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = w)) : mt S g *ᵥ y = y := by
  have hg' := (mem_congGrp _ g).1 hg
  have h0 : (mt S g - 1) *ᵥ y = 0 := by
    funext i
    show ∑ j, (mt S g - 1) i j * y j = 0
    exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_ne h (hg' i j) (hy j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem latV_eq_off {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x)) {L M : Lat S}
    (hm : Moves S g L M (· = w)) : latV S M (· = w) = latV S L (· = w) := by
  ext y
  constructor
  · intro hy
    have hid := latV_idAt hy
    rw [hm y hid, mulVec_eq_of_ne h hg hid]
    exact hy
  · intro hy
    have hid := latV_idAt hy
    have := (hm y hid).1 hy
    rwa [mulVec_eq_of_ne h hg hid] at this

theorem latV_le_of_moves {S : HSp D} {P : Pl D → Prop} {g : GA D S} {L M M' : Lat S} (hm : Moves S g L M P)
    (hm' : Moves S g L M' P) : latV S M P ≤ latV S M' P := by
  intro y hy
  have hid := latV_idAt hy
  have hz : ∀ i, (mt S g⁻¹ *ᵥ y) i ∈ idAt D P := fun i => by
    show ∑ j, mt S g⁻¹ i j * y j ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hid j)
  have he : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one, Matrix.one_mulVec]
  have h1 := (hm _ hz).2 (by rw [he]; exact hy)
  have h2 := (hm' _ hz).1 h1
  rwa [he] at h2

theorem patch : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D),
    ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧
      ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  classical
  intro D S L L' hL hL' Z
  induction Z using Finset.induction_on with
  | empty => exact ⟨L, hL, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ => rfl⟩
  | insert x Z hx ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨g, hg, hgm⟩ := GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace D S M L' hM hL' x
    obtain ⟨M', hM', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M hM).1 g
    refine ⟨M', hM', fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hwx : w = x
      · subst hwx
        exact le_antisymm (latV_le_of_moves (hmv _) hgm) (latV_le_of_moves hgm (hmv _))
      · rw [latV_eq_off hwx hg (hmv _)]
        exact h1 w ((Finset.mem_insert.1 hw).resolve_left hwx)
    · rw [Finset.mem_insert, not_or] at hw
      rw [latV_eq_off hw.1 hg (hmv _)]
      exact h2 w hw.2

end GlobalTheory.FinPl.Patch
