import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.MultiCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def genSet (E : Fin n → Fin n → A) : Set A := Set.range fun p : Fin n × Fin n => E p.1 p.2

theorem gelfA_mem_adjoin (E : Fin n → Fin n → A) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA E k ∈ Algebra.adjoin ℂ (genSet E) := by
  unfold GlobalTheory.SmoothForms.gelfA
  refine Subalgebra.sum_mem _ fun idx _ => Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨a, rfl⟩ := hx
  exact Algebra.subset_adjoin ⟨(_, _), rfl⟩

theorem adjoin_le_centralizer {S T : Set A} (h : ∀ x ∈ S, ∀ y ∈ T, y * x = x * y) :
    Algebra.adjoin ℂ S ≤ Subalgebra.centralizer ℂ T :=
  Algebra.adjoin_le fun x hx => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => h x hx y hy

theorem centre_of_commuting_families_sup (hRC : RelativeCentre) {ι : Type} (X : ι → Fin n → Fin n → A)
    (hX : ∀ i, Formalism.REAL.GlRel (X i)) (hc : ∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b)
    (s : Finset ι) : ∀ C : Subalgebra ℂ A, (∀ i ∈ s, C ≤ Subalgebra.centralizer ℂ (genSet (X i))) →
      ∀ z ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C,
        (∀ i ∈ s, z ∈ Subalgebra.centralizer ℂ (genSet (X i))) →
        z ∈ s.sup (fun i => Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X i)))) ⊔ C := by
  classical
  induction s using Finset.induction_on with
  | empty => intro C _ z hz _; simpa using hz
  | insert w s hw ih =>
    intro C hC z hz hzc
    rw [Finset.sup_insert] at hz ⊢
    have hle : s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C ≤ Subalgebra.centralizer ℂ (genSet (X w)) := by
      refine sup_le (Finset.sup_le fun i hi => adjoin_le_centralizer ?_) (hC w (Finset.mem_insert_self _ _))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc w i (fun h => hw (h ▸ hi)) c d a b
    have hB : ∀ b ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C, ∀ a c, X w a c * b = b * X w a c :=
      fun b hb a c => (Subalgebra.mem_centralizer_iff ℂ).1 (hle hb) _ ⟨(a, c), rfl⟩
    have hz' : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X w p.1 p.2) ⊔
        (s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C) := by
      rw [← sup_assoc]; exact hz
    have h1 := hRC A n (X w) (hX w) _ hB z hz' fun a c =>
      (Subalgebra.mem_centralizer_iff ℂ).1 (hzc w (Finset.mem_insert_self _ _)) _ ⟨(a, c), rfl⟩
    rw [sup_left_comm] at h1
    have hC' : ∀ i ∈ s, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X w))) ⊔ C ≤
        Subalgebra.centralizer ℂ (genSet (X i)) := by
      intro i hi
      refine sup_le ((Algebra.adjoin_le (Set.range_subset_iff.2 fun k => gelfA_mem_adjoin (X w) k)).trans
        (adjoin_le_centralizer ?_)) (hC i (Finset.mem_insert_of_mem hi))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc i w (fun h => hw (h ▸ hi)) c d a b
    have h2 := ih _ hC' z h1 fun i hi => hzc i (Finset.mem_insert_of_mem hi)
    rw [sup_assoc]; rwa [sup_left_comm] at h2

theorem centre_multi : RelativeCentre → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (n : ℕ)
    (X : ι → Fin n → Fin n → A),
    (∀ i, Formalism.REAL.GlRel (X i)) → (∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × Fin n × Fin n => X p.1 p.2.1 p.2.2),
      (∀ i a b, X i a b * z = z * X i a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × ℕ => GlobalTheory.SmoothForms.gelfA (X p.1) p.2) := by
  intro hRC A _ _ ι _ n X hX hc z hz hzc
  classical
  letI := Fintype.ofFinite ι
  have hz' : z ∈ (Finset.univ : Finset ι).sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ ⊥ := by
    rw [sup_bot_eq]
    refine (Algebra.adjoin_le ?_) hz
    rintro _ ⟨⟨i, a, b⟩, rfl⟩
    exact Finset.le_sup (f := fun i => Algebra.adjoin ℂ (genSet (X i))) (Finset.mem_univ i)
      (Algebra.subset_adjoin ⟨(a, b), rfl⟩)
  have h := centre_of_commuting_families_sup hRC X hX hc Finset.univ ⊥ (fun _ _ => bot_le) z hz' fun i _ =>
    (Subalgebra.mem_centralizer_iff ℂ).2 (by rintro _ ⟨⟨a, b⟩, rfl⟩; exact hzc i a b)
  rw [sup_bot_eq] at h
  refine (Finset.sup_le fun i _ => Algebra.adjoin_mono ?_) h
  rintro _ ⟨k, rfl⟩
  exact ⟨(i, k), rfl⟩

end GlobalTheory.LeviHC.MultiCentre
