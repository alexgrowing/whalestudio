import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBotStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutiveStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBoundsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands

open scoped Pointwise in

theorem exists_compact_mod_unipB_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → (∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : V, x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1) → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ v : V, ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g : GL (Fin m) k, l (ρ (corner g) v) ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c := by
  intro k _ _ _ _ ψ hψc hψ1 m V _ _ ρ hs hJ l hl v
  have hcm : ∀ g h : GL (Fin m) k, corner (g * h) = corner g * corner h := fun g h => by
    simp only [corner]
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hcc : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
    (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))
  have hdc : Continuous (diagT k (Fin m)) :=
    (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin m))
  set X : Set V := (fun g => ρ g v) '' (corner '' (KO k (Fin m) : Set (GL (Fin m) k))) with hX
  have hXf : X.Finite := GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt _ V ρ v (hs v) _ (GlobalTheory.SplitFlip.isCompact_KO.image hcc)
  choose r1 hr1 using GlobalTheory.T.whittaker_functional_torus_valuation_bound k ψ hψc hψ1 (m + 1) V ρ hs l hl
  have hlow : ∀ (x : V) (i : Fin m), ∃ r : kˣ, ∀ t : Fin (m + 1) → kˣ,
      l (ρ (diagT k (Fin (m + 1)) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) := by
    intro x i
    have hi := i.2
    have h : ∑ j, ![(i : ℕ) + 1, m - i] j = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact GlobalTheory.T.whittaker_torus_twKer_rootBound' k ψ hψc (m + 1) V ρ l hl _ _ h i.castSucc i.succ (by simp) (by simp) x
      (hJ _ _ h (Nat.succ_pos _) (by omega) x)
  choose r2 hr2 using hlow
  choose R1 R2 hR using fun x => GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds k m (fun _ => r1 x) (r2 x)
  refine ⟨⋃ x ∈ X, diagT k (Fin m) '' {t : Fin m → kˣ | ∀ i, valuation k (R2 x : k) ≤ valuation k (t i : k) ∧
      valuation k (t i : k) ≤ valuation k (R1 x : k)} * (KO k (Fin m) : Set (GL (Fin m) k)),
    hXf.isCompact_biUnion fun x _ => ((GlobalTheory.T.isCompact_boundedTorus' k m (R1 x) (R2 x)).image hdc).mul GlobalTheory.SplitFlip.isCompact_KO,
    fun g hg => ?_⟩
  obtain ⟨u, hu, t, κ, hκ, rfl⟩ := GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral k m g
  have hcu := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
  rw [hcm, hcm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl _ hcu.1, GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one] at hg
  have hg' := right_ne_zero_of_mul hg
  have hxX : ρ (corner κ) v ∈ X := ⟨corner κ, ⟨κ, hκ, rfl⟩, rfl⟩
  have hlast : (Fin.snoc t 1 : Fin (m + 1) → kˣ) (Fin.last m) = 1 := Fin.snoc_last _ _
  have hb := hR _ _ hlast (fun i => ⟨hr2 _ i _ hg', hr1 _ _ i.castSucc i.succ (by simp) hg'⟩)
  refine ⟨u, hu, diagT k (Fin m) t * κ, Set.mem_biUnion hxX ⟨_, ⟨t, fun i => ?_, rfl⟩, κ, hκ, rfl⟩,
    mul_assoc _ _ _⟩
  have := hb i.castSucc
  simpa [Fin.snoc_castSucc] using this

end GlobalTheory.LocLanglands
