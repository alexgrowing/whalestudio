import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

abbrev A (k : Type) [Field k] (N : ℕ) := homogeneousSubmodule (Fin (N + 1)) k

theorem X_mem (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) : (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k j)

theorem X_mem' (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) :
    (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N (1 • 1) := by
  simpa using X_mem k N j

theorem genCover {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) :
    ∃ i : Fin (N + 1), genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) := by
  have htop : ⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, X_mem k N i⟩
    · rw [eq_top_iff]
      intro x hxt; clear hxt
      have hx : x ∈ Algebra.adjoin k (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k)) := by
        rw [MvPolynomial.adjoin_range_X]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem y hy => exact Algebra.subset_adjoin hy
      | algebraMap c =>
        have h0 : (C c : MvPolynomial (Fin (N + 1)) k) ∈ A k N 0 :=
          (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ c)
        have := (Algebra.adjoin (A k N 0) (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k))).algebraMap_mem
          (⟨C c, h0⟩ : A k N 0)
        simpa using this
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
  have hm : ι.base (genericPoint X) ∈ (⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) := by
    rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  exact ⟨i, hi⟩

def away {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) : X.functionField :=
  X.presheaf.germ _ (genericPoint X) h (ι.app _
    (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))

def coordAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) (i : Fin (N + 1))
    (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) : Fin (N + 1) → X.functionField :=
  fun j => away ι (MvPolynomial.X i) (X_mem k N i) h 1 (MvPolynomial.X j) (X_mem' k N j)

def GenAwayEval : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i))
  (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
  away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g

def GenOfAway : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)),
  (∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
    away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g) →
  Gen p ι (coordAt ι i h)

end LateralTheory.EtaleTrace.Cov.GenInPf

namespace LateralTheory.EtaleTrace.Cov
open GenInPf in
theorem GenIn_of (hE : GenAwayEval) (hG : GenOfAway) : GenIn := by
  intro k _ X _ p N ι hp
  obtain ⟨i, h⟩ := genCover ι
  have hgen := hG k p N ι hp i h (hE k p N ι hp i h)
  refine ⟨coordAt ι i h, i, ?_, hgen⟩
  have h1 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).1.mp h
  have h2 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).2 1 (MvPolynomial.X i) (X_mem' k N i) h
  simp only [eval₂_X, pow_one] at h1 h2
  change coordAt ι i h i * coordAt ι i h i = coordAt ι i h i at h2
  exact mul_left_cancel₀ h1 (h2.trans (mul_one _).symm)

end LateralTheory.EtaleTrace.Cov
