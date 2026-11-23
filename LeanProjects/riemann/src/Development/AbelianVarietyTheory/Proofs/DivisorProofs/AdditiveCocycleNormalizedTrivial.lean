import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiperiodicDifferenceSymmetricFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCocycleZeroOfGeneratorsStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.PeriodCocycle

theorem transl_add {g : ℕ} {E : Type} (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ (x + y) P = transl τ x (transl τ y P) := by
  refine Prod.ext rfl ?_
  funext j
  simp only [transl, per, Pi.add_apply, Complex.ofReal_add, Matrix.vecMul, dotProduct, add_mul,
    Finset.sum_add_distrib]
  ring

theorem transl_inr {g : ℕ} {E : Type} (τ : E → Matrix (Fin g) (Fin g) ℂ) (i : Fin g) (P : Pt E g) :
    transl τ (Pi.single (Sum.inr i) (1 : ℝ)) P = (P.1, P.2 + Pi.single i 1) := by
  classical
  refine Prod.ext rfl ?_
  funext j
  simp only [transl, per, Matrix.vecMul, dotProduct, Pi.single_apply, Pi.add_apply]
  split_ifs <;> simp_all

theorem exists_coboundary_add_char : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ H : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (H l) (cov U g)) → (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, H (l + l') P = H l (transl τ l' P) + H l' P) → (∀ i : Fin g, ∀ P ∈ cov U g, H (Pi.single (Sum.inr i) (1 : ℝ)) P = 0) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ ∃ μ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (μ l) V) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ V, μ (l + l') b' = μ l b' + μ l' b') ∧ ∀ l ∈ stdLat g, ∀ P ∈ cov V g, H l P = K (transl τ l P) - K P + μ l P.1 := by
  intro g E _ _ _ U τ hτ H hH hcoc hq b hb
  classical
  have mem_tr : ∀ {W : Set E} (x : Fl g) (P : Pt E g), P ∈ cov W g → transl τ x P ∈ cov W g :=
    fun x P hP => ⟨hP.1, Set.mem_univ _⟩
  have q_mem : ∀ i, (Pi.single i (1 : ℝ) : Fl g) ∈ stdLat g := fun i =>
    Submodule.subset_span ⟨i, by simp⟩
  have hper : ∀ l ∈ stdLat g, ∀ P ∈ cov U g, ∀ i : Fin g,
      H l (P.1, P.2 + Pi.single i 1) = H l P := by
    intro l hl P hP i
    have e1 := hcoc l hl _ (q_mem (Sum.inr i)) P hP
    have e2 := hcoc _ (q_mem (Sum.inr i)) l hl P hP
    rw [hq i P hP, add_zero, transl_inr] at e1
    rw [hq i _ (mem_tr _ _ hP), zero_add, add_comm] at e2
    rw [← e1, e2]
  set h : Fin g → Pt E g → ℂ := fun k => H (Pi.single (Sum.inl k) 1) with hh
  have hrel : ∀ k m, ∀ P ∈ cov U g, h k (transl τ (Pi.single (Sum.inl m) (1 : ℝ)) P) - h k P =
      h m (transl τ (Pi.single (Sum.inl k) (1 : ℝ)) P) - h m P := by
    intro k m P hP
    have e1 := hcoc _ (q_mem (Sum.inl k)) _ (q_mem (Sum.inl m)) P hP
    have e2 := hcoc _ (q_mem (Sum.inl m)) _ (q_mem (Sum.inl k)) P hP
    rw [add_comm] at e2
    simp only [hh]
    linear_combination e2 - e1
  obtain ⟨V, hVo, hbV, hVU, K, hK, hKper, c, hc, hcK⟩ := GlobalTheory.T.quasiperiodic_difference_symmetric_family hτ h (fun k => hH _ (q_mem _))
    (fun k P hP i => hper _ (q_mem _) P hP i) hrel b hb
  have covVU : cov V g ⊆ cov U g := fun P hP => ⟨hVU hP.1, trivial⟩
  refine ⟨V, hVo, hbV, hVU, K, hK, fun l b' => ∑ k, (l (Sum.inl k) : ℂ) * c k b', ?_, ?_, ?_⟩
  · intro l _
    exact DifferentiableOn.fun_sum fun k _ => (hc k).const_mul _
  · intro l _ l' _ b' _
    simp [add_mul, Finset.sum_add_distrib]
  · intro l hl P hP
    have key := GlobalTheory.T.lattice_cocycle_zero_of_generators (U := V) (τ := τ)
      (fun l P => H l P - (K (transl τ l P) - K P + ∑ k, (l (Sum.inl k) : ℂ) * c k P.1))
      ?_ ?_ l hl P hP
    · exact sub_eq_zero.mp key
    · intro l hl l' hl' P hP
      have := hcoc l hl l' hl' P (covVU hP)
      simp only [transl_add, Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
      rw [this]
      simp only [transl]
      ring
    · intro i P hP
      cases i with
      | inl k =>
        have := hcK k P hP
        simp only [hh] at this
        have hs : ∑ j, ((Pi.single (Sum.inl k) (1 : ℝ) : Fl g) (Sum.inl j) : ℂ) * c j P.1 =
            c k P.1 := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hj; simp [Pi.single_apply, hj]
          · simp
        show H _ P - (K _ - K P + ∑ j, ((Pi.single (Sum.inl k) (1 : ℝ) : Fl g) (Sum.inl j) : ℂ) * c j P.1) = 0
        rw [hs, this]
        ring
      | inr i =>
        show H _ P - (K _ - K P + _) = 0
        rw [transl_inr, hKper P hP i, hq i P (covVU hP)]
        simp [Pi.single_apply]

end GlobalTheory.PeriodCocycle
