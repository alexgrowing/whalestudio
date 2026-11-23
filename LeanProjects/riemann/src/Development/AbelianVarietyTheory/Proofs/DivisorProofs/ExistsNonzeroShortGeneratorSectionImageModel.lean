import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelGen

theorem basicOpen_sum_le {X : Scheme.{0}} {U : X.Opens} {ι : Type} (t : Finset ι) (f : ι → Γ(X, U)) :
    X.basicOpen (∑ j ∈ t, f j) ≤ ⨆ j ∈ t, X.basicOpen (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    intro x hx
    have hxU : x ∈ U := X.basicOpen_le _ hx
    rw [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx with h | h
    · have : x ∈ X.basicOpen (f a) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_self a t, this⟩⟩
    · have : x ∈ X.basicOpen (∑ j ∈ t, f j) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ih this)
      obtain ⟨hjt, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_of_mem hjt, hj⟩⟩

theorem exists_mem_nonzeroLocus_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → ∀ x : X, ∃ (j : Fin n) (hj : w j ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s ⟨w j, hj⟩) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ hg x
  have hx : x ∈ (⨆ v, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s v)) := by rw [hM.bpf]; trivial
  obtain ⟨v, hv⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hw : ∀ j, w j ∈ W := fun j => (hg.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ((hg.gen (v : V)).1 v.2)
  have hsum : (v : V) = ∑ j, ((c j : 𝓞 K)) • ((⟨w j, hw j⟩ : W) : V) := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    simp [Int.cast_smul_eq_zsmul]
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  rw [GlobalTheory.T.imageModel_sections_linear_ringOfIntegers K V Ω Nm W ev D X p L ψ s hM hev n (fun j => (c j : 𝓞 K)) (fun j => ⟨w j, hw j⟩) v hsum k] at hk
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (basicOpen_sum_le _ _ hk)
  obtain ⟨-, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
  rw [Scheme.basicOpen_mul] at hj
  exact ⟨j, hw j, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hj.2⟩⟩

end GlobalTheory.ImageModelGen
