import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.SpAlg

variable {K : Type} [Field K] [NumberField K]

theorem places_of_split (hK : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [h₁ : w₁.asIdeal.LiesOver v.asIdeal] [h₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) :
    (∀ u : SemiLocal.PlacesOver K v, u.1 = w₁ ∨ u.1 = w₂) ∧
      Module.finrank (Qv v) (Kv K w₁) = 1 ∧ Module.finrank (Qv v) (Kv K w₂) = 1 := by
  classical
  set u₁ : SemiLocal.PlacesOver K v := ⟨w₁, h₁⟩
  set u₂ : SemiLocal.PlacesOver K v := ⟨w₂, h₂⟩
  have hu : u₁ ≠ u₂ := fun h => hne (congrArg Subtype.val h)
  set f : SemiLocal.PlacesOver K v → ℕ := fun u => Module.finrank (Qv v) (Kv K u.1) with hf
  have hpos : ∀ u, 1 ≤ f u := fun u => Module.finrank_pos
  have hs : ∑ u, f u = 2 := by rw [← hK]; exact SemiLocal.sum_finrank_eq K v
  have h12 : f u₁ + f u₂ ≤ 2 := by
    rw [← hs, ← Finset.sum_pair hu]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have p1 := hpos u₁
  have p2 := hpos u₂
  refine ⟨?_, by show f u₁ = 1; omega, by show f u₂ = 1; omega⟩
  intro u
  by_contra hc
  have c1 : u ≠ u₁ := fun h => hc (Or.inl (congrArg Subtype.val h))
  have c2 : u ≠ u₂ := fun h => hc (Or.inr (congrArg Subtype.val h))
  have h3 : f u + (f u₁ + f u₂) ≤ 2 := by
    rw [← hs, ← Finset.sum_pair hu, ← Finset.sum_insert (by simp [c1, c2])]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have := hpos u
  omega

theorem algebraMap_degreeOneEmbedding_local (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ := by
  have hb := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hy : algebraMap K (Kv K w) ξ ∈ (⊥ : Subalgebra (Qv v) (Kv K w)) := by rw [hb]; trivial
  exact Function.invFun_eq (Algebra.mem_bot.1 hy)

theorem split_place_embeddings_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w₁ w₂ : PlK K)
  [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ ≠ w₂ →
    (∀ ξ : K, algebraMap (Qv v) (Kv K w₁) (dg1 v w₁ ξ) = algebraMap K (Kv K w₁) ξ) ∧
    (∀ ξ : K, algebraMap (Qv v) (Kv K w₂) (dg1 v w₂ ξ) = algebraMap K (Kv K w₂) ξ) ∧
    ∀ ξ : K, dg1 v w₁ ξ * dg1 v w₂ ξ = ((Algebra.norm ℚ ξ : ℚ) : Qv v) := by
  intro K _ _ hK v w₁ w₂ h₁ h₂ hne
  classical
  obtain ⟨hall, hf1, hf2⟩ := places_of_split hK v w₁ w₂ hne
  have s1 := algebraMap_degreeOneEmbedding_local v w₁ hf1
  have s2 := algebraMap_degreeOneEmbedding_local v w₂ hf2
  refine ⟨s1, s2, fun ξ => ?_⟩
  have hu : (⟨w₁, h₁⟩ : SemiLocal.PlacesOver K v) ≠ ⟨w₂, h₂⟩ := fun h => hne (congrArg Subtype.val h)
  have huniv : (Finset.univ : Finset (SemiLocal.PlacesOver K v)) = {⟨w₁, h₁⟩, ⟨w₂, h₂⟩} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hall u with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hn := SemiLocal.algebraMap_norm_eq_prod (K := ℚ) (L := K) v ξ
  rw [huniv, Finset.prod_pair hu] at hn
  simp only [] at hn
  have e1 : Algebra.norm (Qv v) (algebraMap K (Kv K w₁) ξ) = dg1 v w₁ ξ := by
    rw [← s1, Algebra.norm_algebraMap, hf1, pow_one]
  have e2 : Algebra.norm (Qv v) (algebraMap K (Kv K w₂) ξ) = dg1 v w₂ ξ := by
    rw [← s2, Algebra.norm_algebraMap, hf2, pow_one]
  rw [← e1, ← e2]
  refine hn.symm.trans ?_
  exact eq_ratCast (@algebraMap ℚ (Qv v) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)) _

end GlobalTheory.CompanionTheory.SpAlg
