import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

theorem res_mem_Dec {σ : G E' Ω} (hσ : σ ∈ Dec (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Dec (F := E) A := by
  rw [mem_Dec] at hσ ⊢
  refine Eq.trans ?_ hσ
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

theorem res_mem_Ine {σ : G E' Ω} (hσ : σ ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E σ ∈ Ine (F := E) A :=
  ⟨res_mem_Dec hσ.1, hσ.2⟩

theorem res_actsAs {q q' n a b : ℕ} (hq : q' = q ^ n) {σ : G E' Ω} (hσ : ActsAs A q' σ a b) :
    ActsAs A q (AlgEquiv.restrictScalars E σ) (n * a) (n * b) := by
  subst hq
  refine ⟨res_mem_Dec hσ.1, fun x hx => ?_⟩
  rw [pow_mul, pow_mul]
  exact hσ.2 x hx

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

def resW {n : ℕ} (hq : normV w' = normV w ^ n) : Weil h' →* Weil h where
  toFun σ := ⟨AlgEquiv.restrictScalars E (σ : G E' Ω), by
    obtain ⟨a, b, hσ⟩ := σ.2
    exact ⟨n * a, n * b, res_actsAs hq hσ⟩⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

def resI : Ine (F := E') A →* Ine (F := E) A where
  toFun t := ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
