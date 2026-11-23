import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri

theorem independent_and_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  intro Ω _ L _ _ r b b₀ Tm hb hflag hT
  have hspan : Submodule.span Ω (Set.range b₀) = Submodule.span Ω (Set.range b) := by
    have h := hflag r
    unfold flagStep at h
    have e1 : b₀ '' {k : Fin r | (k : ℕ) < r} = Set.range b₀ := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    have e2 : b '' {k : Fin r | (k : ℕ) < r} = Set.range b := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    rw [e1, e2] at h
    exact h.symm
  have hb₀ : LinearIndependent Ω b₀ := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range b₀))
    rw [hspan, finrank_span_eq_card hb]
  refine ⟨hb₀, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h := hflag ((i : ℕ) + 1)
    unfold flagStep at h
    rw [← h]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  obtain ⟨c, hc, hcb⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hmem
  have hsum : ∑ k, (c k - Tm i k) • b₀ k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hT i, ← hcb, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp
    · intro k
      simp
  have h0 : c j - Tm i j = 0 := (Fintype.linearIndependent_iff.mp hb₀) (fun k => c k - Tm i k) hsum j
  have hcj : c j = 0 := by
    by_contra hne
    have hsupp := (Finsupp.mem_supported Ω c).mp hc
    have hj : j ∈ ({k : Fin r | (k : ℕ) < (i : ℕ) + 1} : Set (Fin r)) :=
      hsupp (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
    have hj' : (j : ℕ) < (i : ℕ) + 1 := hj
    have hij' : (i : ℕ) < (j : ℕ) := hij
    omega
  rw [hcj, zero_sub, neg_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri
