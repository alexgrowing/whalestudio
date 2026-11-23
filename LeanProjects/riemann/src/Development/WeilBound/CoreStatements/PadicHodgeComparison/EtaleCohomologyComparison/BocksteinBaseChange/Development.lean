import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.HodgeTateFromSandwich

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def SeamAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Good D ∧ D.Span Model.Good (Bst l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

theorem smooth_of (h1 : PeriodRingFacts) (h2 : BcrisRegularPeriodRing) (h3 : ComparisonPairing) (h4 : ComparisonInjectiveStrict) (h5 : ComparisonAdmissible) (h6 : EtaleSideSmoothAndSemistable)
    (hI : ZIn) (hS : SeamS) : SmoothModelCrystalline ∧ DeRhamComparisonSmooth := by
  constructor
  · intro l _ K _ M hM hs n a b
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hS l K
    obtain ⟨P, hP⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).1 hL e β κ
    exact h5 l K _ _ P _ (h2 l K) M ⟨hM, hs⟩ n (h4 l K _ _ P (h1 l K) (h6 hI l K).1 M ⟨hM, hs⟩ n).1
      (hP _ _ (t_inv_mem l) (h2 l K).q_mem hsp M ⟨hM, hs⟩ ⟨hM, hs⟩ n) a b
  · intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hS l K
    obtain ⟨P, -⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).1 hL e β κ
    exact ⟨P.cmp (h6 hI l K).1 (h4 l K _ _ P (h1 l K) (h6 hI l K).1)⟩

theorem bcr_le_bst (l : ℕ) [Fact l.Prime] : Bcr l ≤ Bst l :=
  Subring.closure_mono (Set.union_subset_union_right _ (by
    intro x hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)))

theorem narrow_of (h1 : PeriodRingFacts) (h2 : BcrisRegularPeriodRing) (h2' : BstRegularPeriodRing) (h3 : ComparisonPairing) (h4 : ComparisonInjectiveStrict) (h5 : ComparisonAdmissible) (h6 : EtaleSideSmoothAndSemistable)
    (hI : ZIn) (hS : SeamS) (hA : SeamAll) : CstNarrow ∧ DeRhamComparisonSemistable := by
  have hd : DeRhamComparisonSemistable := by
    intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hA l K
    obtain ⟨P, -⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).2 hL e β κ
    exact ⟨P.cmp (h6 hI l K).2 (h4 l K _ _ P (h1 l K) (h6 hI l K).2)⟩
  refine ⟨⟨?_, (smooth_of h1 h2 h3 h4 h5 h6 hI hS).1, hd.dr⟩, hd⟩
  intro l _ K _ M hM n a b
  obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hA l K
  obtain ⟨P, hP⟩ := h3 l K _ _ D (h1 l K) (h6 hI l K).2 hL e β κ
  exact h5 l K _ _ P _ (h2' l K) M hM n (h4 l K _ _ P (h1 l K) (h6 hI l K).2 M hM n).1
    (hP _ _ (bcr_le_bst l (t_inv_mem l)) (h2' l K).q_mem hsp M hM hM n) a b

end CrystallineSemistableComparison
