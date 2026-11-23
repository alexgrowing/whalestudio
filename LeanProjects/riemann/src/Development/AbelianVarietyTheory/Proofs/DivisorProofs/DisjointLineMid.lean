import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ConeSmallSer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def StabLn (x : Fin n → E) (g : UA σ J) : Prop :=
  ∃ l : (AE F E)ˣ, mat g *ᵥ incV F x = l.1 • incV F x

def OrthLn (x : Fin n → E) (g : UA σ J) : Prop :=
  (mat g⁻¹ *ᵥ incV F x) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F x i)) = 0

def lineSet (x : Fin n → E) (T : Set (UA σ J)) : Set (UA σ J) := {t | t ∈ T ∧ StabLn x t}

def midSet (x : Fin n → E) (T : Set (UA σ J)) : Set (UA σ J) := {t | t ∈ T ∧ ¬ StabLn x t ∧ OrthLn x t}

def bigSet (x : Fin n → E) (T : Set (UA σ J)) : Set (UA σ J) := {t | t ∈ T ∧ ¬ StabLn x t ∧ ¬ OrthLn x t}

def partSum (f : UA σ J → ℂ) (S : Set (UA σ J)) (h : UA σ J) : ℂ := ∑' t : S, f (t.1 * h)

theorem union_eq (x : Fin n → E) (T : Set (UA σ J)) :
    T = lineSet x T ∪ midSet x T ∪ bigSet x T := by
  ext t
  simp only [lineSet, midSet, bigSet, Set.mem_union, Set.mem_setOf_eq]
  by_cases h1 : StabLn x t <;> by_cases h2 : OrthLn x t <;> tauto

theorem disjoint_line_mid (x : Fin n → E) (T : Set (UA σ J)) : Disjoint (lineSet x T) (midSet x T) :=
  Set.disjoint_left.2 fun _ h1 h2 => h2.2.1 h1.2

theorem disjoint_lm_big (x : Fin n → E) (T : Set (UA σ J)) :
    Disjoint (lineSet x T ∪ midSet x T) (bigSet x T) :=
  Set.disjoint_left.2 fun _ h1 h2 => by
    rcases h1 with h1 | h1
    · exact h2.2.1 h1.2
    · exact h2.2.2 h1.2.2

theorem tsum_eq_three (x : Fin n → E) (T : Set (UA σ J)) (f : UA σ J → ℂ) (h : UA σ J)
    (hs : Summable fun t : T => f (t.1 * h)) :
    ∑' t : T, f (t.1 * h) = partSum f (lineSet x T) h + partSum f (midSet x T) h + partSum f (bigSet x T) h := by
  set g : UA σ J → ℂ := fun t => f (t * h) with hg
  have hsub : ∀ S ⊆ T, Summable (g ∘ ((↑) : S → UA σ J)) := by
    intro S hST
    have hind : Summable (T.indicator g) := summable_subtype_iff_indicator.1 hs
    exact (hind.subtype S).congr fun t => Set.indicator_of_mem (hST t.2) g
  have hLT : lineSet x T ⊆ T := fun t ht => ht.1
  have hMT : midSet x T ⊆ T := fun t ht => ht.1
  have hBT : bigSet x T ⊆ T := fun t ht => ht.1
  change ∑' t : T, g t = _
  rw [tsum_congr_set_coe g (union_eq x T), Summable.tsum_union_disjoint (disjoint_lm_big x T)
      (hsub _ (Set.union_subset hLT hMT)) (hsub _ hBT),
    Summable.tsum_union_disjoint (disjoint_line_mid x T) (hsub _ hLT) (hsub _ hMT)]
  rfl

end GlobalTheory.ConeSmallSer

end
