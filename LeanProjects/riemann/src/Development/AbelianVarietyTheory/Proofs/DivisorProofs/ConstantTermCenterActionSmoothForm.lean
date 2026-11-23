import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology

namespace GlobalTheory.ConstTermZalg

open GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem good_add {φ ψ : Sm E a} (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1, hψ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      (Filter.inter_mem (hφ.2.mem_nhds (by simp)) (hψ.2.mem_nhds (by simp))) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := hk
    have h1' : finRep E a k φ = φ := h1
    have h2' : finRep E a k ψ = ψ := h2
    show finRep E a k (φ + ψ) = φ + ψ
    rw [map_add, h1', h2']

theorem good_smul {φ : Sm E a} (hφ : Good φ) (s : ℂ) : Good (s • φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hφ.2.mem_nhds (by simp)) fun k hk => ?_)
    have h1' : finRep E a k φ = φ := hk
    show finRep E a k (s • φ) = s • φ
    rw [map_smul, h1']

theorem good_integrable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν] {φ : Sm E a} (h : Good φ) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) ν := by
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.2
  exact integrable_unip ν (Ψ := fun g (_ : Lie E a) => φ.1 g) (hc.comp continuous_fst).continuousOn
    (fun γ g => funext fun _ => h.1 γ g) g (y := oneL E a) isUnit_one

theorem constTerm_zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hH hF h1 φ hl ho z hz c hc
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  let CT : Sm E a → GA E a → ℂ := fun ψ g => ∫ x, ψ.1 (unip x * g) ∂(μ.restrict 𝓕)
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ ψ, Good ψ → Good (z ψ) ∧ ∀ c : Sm E a, c.1 = CT ψ → (z c).1 = CT (z ψ)}
      mul_mem' := by
        intro z w hz hw ψ h
        exact ⟨(hz _ (hw ψ h).1).1, fun c hc => (hz _ (hw ψ h).1).2 _ ((hw ψ h).2 c hc)⟩
      add_mem' := by
        intro z w hz hw ψ h
        refine ⟨good_add (hz ψ h).1 (hw ψ h).1, fun c hc => ?_⟩
        have e1 := (hz ψ h).2 c hc
        have e2 := (hw ψ h).2 c hc
        funext g
        simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, e1, e2, CT]
        rw [integral_add (good_integrable _ (hz ψ h).1 g) (good_integrable _ (hw ψ h).1 g)]
      algebraMap_mem' := by
        intro s ψ h
        simp only [Module.algebraMap_end_apply]
        refine ⟨good_smul h s, fun c hc => ?_⟩
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, hc, CT, smul_eq_mul]
        rw [integral_const_mul] }
  have hlie : ∀ X, lie E a X ∈ S := fun X ψ h => ⟨h.lie X, fun c hc => funext fun g => by
    rw [lie_apply, hc]
    exact (constTerm_mem_Sm E a r μ 𝓕 hH hF h1 ψ h.1 h.2).2 X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hlie _) (S.smul_mem (hlie _) _)) _
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, ho⟩).2 c hc

end GlobalTheory.ConstTermZalg
