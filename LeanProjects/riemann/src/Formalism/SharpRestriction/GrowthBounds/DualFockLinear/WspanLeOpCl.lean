import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestNDOfAdm

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section Words

variable {R : Type} [CommRing R] {n' k : ℕ}

def WSpan (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) :
    Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ l' : List (Fin n' × (Fin k × Fin k)), l'.map Prod.fst = l.map Prod.fst ∧ y = opWord l' h}

theorem wspan_op (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) (s : Fin n')
    (x : Fin k × Fin k) (c c' : Fin k) {z : MvPolynomial (Fin n' × Fin k) R} (hz : z ∈ WSpan l h) :
    X (s, c) * pderiv (s, c') z ∈ WSpan ((s, x) :: l) h := by
  unfold WSpan at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l', hl', rfl⟩ := hy
    exact Submodule.subset_span ⟨(s, (c, c')) :: l', by simp [hl'], rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, mul_add]
    exact Submodule.add_mem _ ha hb
  | smul a y _ hy =>
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ a hy

theorem Lin_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ WSpan l (Lin N f) := by
  intro l
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons y l ih =>
    obtain ⟨s, a, b⟩ := y
    show Lin N (X (s, a) * pderiv (s, b) (opWord l f)) ∈ _
    rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b' _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [mul_smul_comm, MvPolynomial.C_mul', smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (wspan_op l _ s (a, b) b' c ih))

theorem wspan_le_OpCl (TT : Finset (Fin n')) (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R))
    (l : List (Fin n' × (Fin k × Fin k))) (h1 : ∀ z ∈ l, z.1 ∈ TT) (h2 : ∀ s, (l.filter fun z => z.1 = s).length ≤ c)
    {h : MvPolynomial (Fin n' × Fin k) R} (hh : h ∈ M) : WSpan l h ≤ OpCl TT c M := by
  rw [WSpan, Submodule.span_le]
  rintro y ⟨l', hl', rfl⟩
  refine Submodule.subset_span ⟨h, hh, l', ?_, ?_, rfl⟩
  · intro z hz
    have hz' : z.1 ∈ l.map Prod.fst := hl' ▸ List.mem_map_of_mem hz
    obtain ⟨z', hz'', e⟩ := List.mem_map.1 hz'
    exact e ▸ h1 z' hz''
  · intro s
    have e : ∀ L : List (Fin n' × (Fin k × Fin k)), (L.filter fun z => decide (z.1 = s)).length =
        ((L.map Prod.fst).filter fun t => decide (t = s)).length := by
      intro L
      rw [List.filter_map, List.length_map]
      rfl
    rw [e, hl', ← e]
    exact h2 s

theorem Lin_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (TT : Finset (Fin n')) (c : ℕ)
    (M M' : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ M') :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ OpCl TT c M' := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact wspan_le_OpCl TT c M' l h1 h2 (hM f0 hf0) (Lin_word N N' h f0 l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Words

end Formalism.MainNotions.TestSideCounting
