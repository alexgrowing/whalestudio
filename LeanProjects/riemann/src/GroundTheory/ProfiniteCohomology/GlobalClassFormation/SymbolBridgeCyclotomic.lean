import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeSum
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicCompositum
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.RationalDiagonal
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal

theorem sup_rootsOfUnityField_mono (F : IntermediateField ℚ ℚ̄) {m n : ℕ} (h : m ∣ n) :
    F ⊔ Cyclotomic.rootsOfUnityField m ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ _ _ fun x hx ↦ ?_) F
  obtain ⟨c, rfl⟩ := h
  change x ^ (m * c) = 1
  rw [pow_mul, show x ^ m = 1 from hx, one_pow]

theorem exists_le_sup_rootsOfUnityField (F E : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ E]
    (hE : E ≤ F ⊔ Cyclotomic.maxCyclotomic) :
    ∃ n : ℕ+, E ≤ F ⊔ Cyclotomic.rootsOfUnityField n := by
  set T : ℕ+ → IntermediateField ℚ ℚ̄ := fun n ↦ F ⊔ Cyclotomic.rootsOfUnityField n with hT
  have hdir : Directed (· ≤ ·) T := fun m n ↦
    ⟨m * n, sup_rootsOfUnityField_mono F (by simp), sup_rootsOfUnityField_mono F (by simp)⟩
  have hsup : F ⊔ Cyclotomic.maxCyclotomic = ⨆ n, T n := by
    rw [Cyclotomic.maxCyclotomic_eq_iSup, sup_iSup]
  set b := Module.finBasis ℚ E with hb
  have hmem : ∀ i, ∃ n, ((b i : E) : ℚ̄) ∈ T n := fun i ↦ by
    have h := hE (b i).2
    rw [hsup, ← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  choose n hn using hmem
  obtain ⟨z, hz⟩ := hdir.finset_le (Finset.univ.image n)
  refine ⟨z, fun x hx ↦ ?_⟩
  have hbT : ∀ i, ((b i : E) : ℚ̄) ∈ T z := fun i ↦
    hz (n i) (Finset.mem_image_of_mem n (Finset.mem_univ i)) (hn i)
  have hx' : (⟨x, hx⟩ : E) ∈ Submodule.span ℚ (Set.range b) := b.mem_span _
  have hmap := Submodule.mem_map_of_mem (f := E.val.toLinearMap) hx'
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  exact (Submodule.span_le (p := (T z).toSubalgebra.toSubmodule)).2
    (by rintro _ ⟨i, rfl⟩; exact hbT i) hmap

variable {K : FiniteSubfield} (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

theorem ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (a : K.1ˣ) : ideleSymbol K.1 E.1 (diagonal K.1 a) = 1 := by
  obtain ⟨n, hn⟩ := exists_le_sup_rootsOfUnityField K.1 E.1 hE
  have : FiniteDimensional ℚ (Cyclotomic.rootsOfUnityField n) :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} ℚ _
  set F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField n, inferInstance⟩ with hF
  have : IsCyclotomicExtension {(n : ℕ)} ℚ F.1 :=
    (inferInstance : IsCyclotomicExtension {(n : ℕ)} ℚ (Cyclotomic.rootsOfUnityField n))
  have : IsGalois ℚ F.1 := IsCyclotomicExtension.isGalois {(n : ℕ)} ℚ F.1
  have : IsMulCommutative (F.1 ≃ₐ[ℚ] F.1) := IsCyclotomicExtension.isMulCommutative {(n : ℕ)} ℚ F.1
  set M := CyclotomicSymbol.compositum K F with hM
  have : Fact (E ≤ M) := ⟨hn⟩
  have : IsScalarTower K.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hMone : ideleSymbol K.1 M.1 (diagonal K.1 a) = 1 := by
    have h := CyclotomicSymbol.restrictHom_eq_ideleSymbol K F 1 (diagonal K.1 a) (by
      rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one F.1 {(n : ℕ)}]
      exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1))
    rw [← h, map_one]
  rw [← restrictNormal_ideleSymbol E.1 M.1, hMone]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := M.1) E.1)

variable (ι : LocalEmbeddings K)

theorem finsum_char_localSymbolAt_eq_zero (hE : E.1 ≤ K.1 ⊔ Cyclotomic.maxCyclotomic)
    (χ : Additive K.1.fixingSubgroup →ₜ+ QZ)
    (hχ : ∀ h : K.1.fixingSubgroup, (h : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ E.1.fixingSubgroup → χ (Additive.ofMul h) = 0)
    (a : K.1ˣ) :
    ∑ᶠ v : Place K.1, χ (Additive.ofMul (localSymbolAt ι v a)) = 0 := by
  rw [finsum_char_localSymbolAt_eq ι E χ hχ a 1
    (by rw [map_one, ideleSymbol_diagonal_eq_one_of_le_sup_maxCyclotomic E hE a]), ofMul_one, map_zero]

end

end GroundTheory.ProfCoh
