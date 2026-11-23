import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorRightOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzProductDecompositionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
open GlobalTheory.SliceSchwartz
open scoped RestrictedProduct

open scoped Classical

noncomputable section

namespace GlobalTheory.TamePartR

theorem td_of_inj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnected_finiteAdele : ∀ (F : Type) [Field F] [NumberField F], TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v
  haveI : TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]) :=
    td_of_inj (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem pureA_sum (F : Type) [Field F] [NumberField F] {κ ι : Type} [Fintype ι] (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (∑ i, g i) = ∑ i, pureA F f (g i) := by
  funext x
  simp [pureA, Finset.sum_apply, Finset.mul_sum]

theorem isTame_partR : ∀ (F : Type) [Field F] [NumberField F] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ)), IsTame F T → IsTame F (partR (κ := κ) T) := by
  intro F _ _ κ κ' κ₁' _ _ _ T hT g hg
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele (F := F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField (F := F)
  haveI := totallyDisconnected_finiteAdele F
  obtain ⟨ι₀, _, g₁, g₂, hg₁, hg₂, rfl⟩ := GlobalTheory.T.schwartz_product_decomposition _ κ κ' g hg
  choose ι inst P g' hg' hP using fun i => hT (g₂ i) (hg₂ i)
  choose Q hQ using fun (p : Σ i, ι i) => GlobalTheory.T.schwartz_tensor_right_operator (mixedEmbedding.mixedSpace F) κ κ' κ₁' (P p.1 p.2)
  refine ⟨Σ i, ι i, inferInstance, Q, fun p z => g₁ p.1 (z ∘ Sum.inl) * g' p.1 p.2 (z ∘ Sum.inr),
    fun p => GlobalTheory.SchwartzBox.sb_box (hg₁ p.1) (hg' p.1 p.2), fun f => ?_⟩
  rw [pureA_sum, map_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext s
  rw [partR_apply, Finset.sum_apply]
  set xa : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (s (Sum.inl k)).1
  have hfun : (fun x₂ => pureA F f (fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr)) (Sum.elim (s ∘ Sum.inl) x₂)) =
      g₁ i (fun k => (s (Sum.inl k)).2) • pureA F (sliceR f xa) (g₂ i) := by
    funext x₂
    simp only [pureA, Pi.smul_apply, smul_eq_mul, sliceR_apply]
    have e : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((Sum.elim (s ∘ Sum.inl) x₂ : κ ⊕ κ' → AF F) k).1) =
        Sum.elim xa (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₂ k).1) := by
      funext k; cases k <;> rfl
    rw [e]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    ring
  rw [hfun, map_smul, hP i (sliceR f xa)]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pureA, hQ]
  simp only [Function.comp_def]
  ring

end GlobalTheory.TamePartR
