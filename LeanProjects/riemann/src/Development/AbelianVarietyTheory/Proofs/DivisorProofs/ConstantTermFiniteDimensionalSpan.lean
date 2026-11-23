import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceContinuousInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowthStatement
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem slice_cpt_mem {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ} (hr : r ≤ a)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) [MeasurableSpace (BlockIx a r → Ad E)]
    [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (φ : Sm E a) (hφ : φ ∈ GlobalTheory.HCF.formsGL E a L W X N) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (g : GA E (a - r)) :
    (fun k : Kinf E (a - r) => slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k))) ∈
      ktypeSub hr κ W := by
  have hm := GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ (Submodule.subset_span hφ)
    (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ))
  refine ⟨_, hm, ?_⟩
  funext k
  exact (slice_mul_cpt μ 𝓕 hr φ.1 m₁ t κ g k).symm

end GlobalTheory.SliceTwo

namespace GlobalTheory.HCFct

open GlobalTheory.SliceTwo

theorem slice2_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (L' : Subgroup (GL (Fin (a - r)) (Af E))) (W' : Submodule ℂ (Kinf E (a - r) → ℂ)), IsOpen (L' : Set (GL (Fin (a - r)) (Af E))) ∧ FiniteDimensional ℂ W' ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∃ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧ (∀ γ g, ψ.1 (ratGL E (a - r) γ * g) = ψ.1 g) ∧ IsOpen {k | finRep E (a - r) k ψ = ψ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) ∧ (∀ g, ∃ (C : ℝ) (M : ℕ), ∀ y, ‖ψ.1 (g * infGL E (a - r) y)‖ ≤ C * height y ^ M) ∧ (∀ k ∈ L', finRep E (a - r) k ψ = ψ) ∧ ∀ g : GA E (a - r), (fun k : Kinf E (a - r) => (cptRep E (a - r) k ψ).1 g) ∈ W' := by
  intro E _ _ _ a L hL W hW X _ N r _ hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  refine ⟨levelSub hr.le t L, ktypeSub hr.le κ W, GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup E a r hr.le t L hL, inferInstance, fun φ hφ m₁ => ?_⟩
  have hA : IsAutForm φ := hφ.1
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hA.level
  have hfix : ∀ k ∈ L, ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun k hk g =>
    congrFun (congrArg Subtype.val (hφ.2.1 k hk)) g
  let ψ : Sm E (a - r) := ⟨slice E μ 𝓕 hr.le φ.1 m₁ t κ, GlobalTheory.T.constant_term_slice_cusp_form E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ⟩
  have hlev : ∀ k ∈ levelSub hr.le t L, finRep E (a - r) k ψ = ψ := fun k hk =>
    Subtype.ext (funext fun g => slice_mul_finGL μ 𝓕 hr.le φ.1 L hfix m₁ t κ k hk g)
  refine ⟨ψ, rfl, GlobalTheory.T.constant_term_slice_continuous_invariant E a r hr.le μ 𝓕 hμ h𝓕 h1 φ.1 hc hA.left m₁ t κ, ?_,
    GlobalTheory.T.constant_term_slice_levi_restriction E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ ψ rfl, GlobalTheory.T.constant_term_slice_levi_moderate_growth E a r hr.le μ 𝓕 hμ h𝓕 h1 φ hA m₁ t κ, hlev,
    fun g => slice_cpt_mem hr.le L W hW X N μ 𝓕 hμ h𝓕 h1 φ hφ m₁ t κ g⟩
  refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup E a r hr.le t L hL).mem_nhds (Subgroup.one_mem _)) fun k hk => hlev k hk)

end GlobalTheory.HCFct

end
