import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BlockRootsCuspidal

open Polynomial

noncomputable section

namespace GlobalTheory.Proof.ListFormLabels

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.BlockRootsCuspidal

theorem blocks_iff {F : Type} [Monoid F] (g : ℕ) (B : Multiset (ℕ × ℕ)) (Rt : Multiset F) :
    (∃ L : List (ℕ × ℕ × Multiset F),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = B ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ g) = p.2.2) ∧
      Rt = (L.map fun p => p.2.1 • p.2.2).sum) ↔ IsBlockRoots g B Rt := by
  constructor
  · rintro ⟨L, h1, h2, h3⟩
    refine ⟨((L.map fun p => ((p.1, p.2.1), p.2.2) : List ((ℕ × ℕ) × Multiset F)) : Multiset _), ?_, ?_, ?_⟩
    · rw [← h1, Multiset.map_coe, List.map_map]; rfl
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
      exact h2 q hq
    · rw [h3, Multiset.map_coe, Multiset.sum_coe, List.map_map]; rfl
  · rintro ⟨M, h1, h2, h3⟩
    induction M using Quotient.inductionOn with
    | _ M =>
    refine ⟨M.map fun p => (p.1.1, p.1.2, p.2), ?_, ?_, ?_⟩
    · rw [← h1, List.map_map]; rfl
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h2 q (Multiset.mem_coe.2 hq)
    · rw [← h3, List.map_map]
      exact Multiset.sum_coe _

theorem tameGen_tg (D : D7) (k : Fin 2) (v : D.nd.PlG k) :
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) :=
  (D.ntypes.tg_gen k v).2

def ListFormAt (D : D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∃ L : List (ℕ × ℕ × Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = D.ntypes.bc σ ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ D.host.g k) = p.2.2) ∧
      Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v) = (L.map fun p => p.2.1 • p.2.2).sum) ∧
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : Formalism.MainNotions.N.GE D.nd,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

theorem listForm_iff_forall (D : D7) : Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔ ∀ σ k v, ListFormAt D σ k v := Iff.rfl

theorem clause_iff (D : D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) :
    ListFormAt D σ k v ↔
      (BlockRootsAt D σ k v ∧
        (D.ntypes.cuspidal σ → ∀ lam : D.what₂.places.Pl, D.what₂.places.resChar lam ≠ D.host.g k →
          TameAt D σ k v lam)) :=
  and_congr (blocks_iff _ _ _)
    (forall_congr' fun _ => ⟨fun h => h (tameGen_tg D k v), fun h _ => h⟩)

theorem labels_iff_listForm_good (D : D7) :
    LabelsAndTameInertia D ↔ ∀ σ, D.nd.goodRow σ → ∀ k v, ListFormAt D σ k v :=
  forall_congr' fun σ => forall_congr' fun _ => forall_congr' fun k => forall_congr' fun v =>
    (clause_iff D σ k v).symm

theorem labels_of_listForm (D : D7) (h : Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D) : LabelsAndTameInertia D :=
  (labels_iff_listForm_good D).2 fun σ _ k v => h σ k v

theorem listForm_iff_labels_and_bad (D : D7) :
    Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔
      LabelsAndTameInertia D ∧ ∀ σ, ¬ D.nd.goodRow σ → ∀ k v, ListFormAt D σ k v := by
  refine ⟨fun h => ⟨labels_of_listForm D h, fun σ _ k v => h σ k v⟩, fun ⟨h₁, h₂⟩ σ k v => ?_⟩
  by_cases hσ : D.nd.goodRow σ
  · exact (labels_iff_listForm_good D).1 h₁ σ hσ k v
  · exact h₂ σ hσ k v

theorem listForm_iff_labels (D : D7) (hD : GoodFTAll D) :
    Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔ LabelsAndTameInertia D :=
  ⟨labels_of_listForm D, fun h σ k v => (labels_iff_listForm_good D).1 h σ (hD σ) k v⟩

theorem comparison (D : D7) :
    (Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔ ∀ σ k v, ListFormAt D σ k v) ∧
    (LabelsAndTameInertia D ↔ ∀ σ, D.nd.goodRow σ → ∀ k v, ListFormAt D σ k v) ∧
    (Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D → LabelsAndTameInertia D) ∧
    (GoodFTAll D → (Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔ LabelsAndTameInertia D)) :=
  ⟨listForm_iff_forall D, labels_iff_listForm_good D, labels_of_listForm D, listForm_iff_labels D⟩

end GlobalTheory.Proof.ListFormLabels
