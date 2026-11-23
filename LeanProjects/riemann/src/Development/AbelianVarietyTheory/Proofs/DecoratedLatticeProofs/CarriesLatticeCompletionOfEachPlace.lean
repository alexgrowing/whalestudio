import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesPl

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPl.KOpen

variable {D : D7}

theorem latV_transfer (S : HSp D) (L : Lat S) {P₁ P₂ : Pl D → Prop} (h : ∀ p, P₁ p → P₂ p)
    {z : Fin S.rank → AE D} (hz : ∀ i, z i ∈ idAt D P₁) : z ∈ latV S L P₁ ↔ z ∈ latV S L P₂ := by
  rw [mem_latV_iff S L P₁ z hz, mem_latV_iff S L P₂ z fun i => idAt_mono h (hz i)]

theorem mem_latV_empty (S : HSp D) (L : Lat S) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· ∈ (∅ : Finset (Pl D)))) : z ∈ latV S L (· ∈ (∅ : Finset (Pl D))) := by
  classical
  rw [mem_latV_iff S L _ z hz]
  have h0 : finPart D ∘ z = 0 := by
    funext i
    rw [Function.comp_apply, ← e_mul_fin (hz i)]
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
    rw [map_mul, compFin_e, if_neg (Finset.notMem_empty w), zero_mul, Pi.zero_apply, map_zero]
  rw [h0]
  exact zero_mem _

theorem moves_of_places : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : Lat S) (Q : Finset (Pl D)),
    (∀ v ∈ Q, Moves S g L M (· = v)) → Moves S g L M (· ∈ Q) := by
  intro D S g L M Q
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro _ y hy
    exact iff_of_true (mem_latV_empty S L hy) (mem_latV_empty S M (supp_mulVec S _ g hy))
  | insert v Q hv ih =>
    intro hQ y hy
    have hQ' := ih fun w hw => hQ w (Finset.mem_insert_of_mem hw)
    have hvv := hQ v (Finset.mem_insert_self v Q)
    have hgy := supp_mulVec S _ g hy
    have comm : ∀ c : AE D, c • (mt S g *ᵥ y) = mt S g *ᵥ (c • y) := fun c => (mulVec_smul _ _ _).symm
    have s1 : ∀ i, (eQ {v} • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (eQ_off {v}) (hy i)
    have s2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (one_sub_eQ_off {v}) (hy i)
    have i1 : ∀ p, (p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) → p = v := fun p h => Finset.mem_singleton.1 h.2
    have i2 : ∀ p, (p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) → p ∈ Q := fun p h =>
      (Finset.mem_insert.1 h.1).resolve_left fun e => h.2 (Finset.mem_singleton.2 e)
    have t1 : ∀ i, (eQ {v} • y) i ∈ idAt D (· = v) := fun i => idAt_mono i1 (s1 i)
    have t2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (· ∈ Q) := fun i => idAt_mono i2 (s2 i)
    rw [mem_latV_iff_parts S L _ {v} hy, mem_latV_iff_parts S M _ {v} hgy, comm, comm,
      latV_transfer S L i1 s1, latV_transfer S L i2 s2,
      latV_transfer S M i1 (fun i => by rw [← comm]; exact mul_mem_idAt (eQ_off {v}) (hgy i)),
      latV_transfer S M i2 (fun i => by rw [← comm]; exact mul_mem_idAt (one_sub_eQ_off {v}) (hgy i))]
    exact and_congr (hvv _ t1) (hQ' _ t2)

end GlobalTheory.FinPl.MovesPl

end
