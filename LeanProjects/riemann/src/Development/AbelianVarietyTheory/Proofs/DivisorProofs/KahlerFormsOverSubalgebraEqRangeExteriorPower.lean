import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem smul_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    {b : K} (hb : b ∈ B) {y : DR k K} (hy : y ∈ omB k K B q) : b • y ∈ omB k K B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨b * c, B.mul_mem hb hc, v, hv, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul r y _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h

theorem ιMulti_D_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    (w : Fin q → B) : (ExteriorAlgebra.ιMulti K q fun j => D k K (w j : K)) ∈ omB k K B q := by
  apply Submodule.subset_span
  exact ⟨1, B.one_mem, fun j => (w j : K), fun j => (w j).2, (one_smul K _).symm⟩

theorem omB_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K,
    Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧
    ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  intro k K _ _ _ B _ _ q
  haveI : Algebra.FormallyEtale B K := .of_isLocalization (nonZeroDivisors B)
  let φ : Ω[B⁄k] →ₗ[B] Ω[K⁄k] := KaehlerDifferential.map k k B K
  have hD : ∀ x : B, φ (D k B x) = D k K (x : K) := fun x => KaehlerDifferential.map_D k k B K x
  have hφ : IsBaseChange K φ := IsBaseChange.of_equiv (tensorKaehlerEquivOfFormallyEtale k B K) fun x => by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl
  let E := GlobalTheory.exteriorPowerMapOver K q φ
  have hE : IsLocalizedModule (nonZeroDivisors B) E :=
    (isLocalizedModule_iff_isBaseChange _ K E).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ q)
  haveI : Module.Projective B (⋀[B]^q Ω[B⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective B Ω[B⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination B id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat B (⋀[B]^q Ω[B⁄k]) := inferInstance
  haveI : Module.IsTorsionFree B (⋀[B]^q Ω[B⁄k]) := Module.Flat.isTorsionFree
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors B) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[B]^q Ω[B⁄k])
      (isRegular_of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  let e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K := ((⋀[K]^q Ω[K⁄k]).subtype.restrictScalars B) ∘ₗ E
  have hι : ∀ a : Fin q → Ω[B⁄k], e (exteriorPower.ιMulti B q a) =
      ExteriorAlgebra.ιMulti K q fun j => φ (a j) := by
    intro a
    change ((E (exteriorPower.ιMulti B q a) : ⋀[K]^q Ω[K⁄k]) : DR k K) = _
    rw [GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.ιMulti_apply_coe]
  have hιD : ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
    intro v
    rw [hι]
    simp only [hD]
  have hB : ∀ (b : B) (y : DR k K), b • y = (b : K) • y := fun b y => (algebraMap_smul K b y).symm
  refine ⟨e, Subtype.val_injective.comp hEinj, fun y => ⟨fun hy => ?_, ?_⟩, hιD⟩
  · have : omB k K B q ≤ LinearMap.range (e.restrictScalars k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      refine ⟨(⟨b, hb⟩ : B) • exteriorPower.ιMulti B q (fun j => D k B ⟨v j, hv j⟩), ?_⟩
      rw [LinearMap.restrictScalars_apply, map_smul, hιD, hB]
    obtain ⟨z, hz⟩ := this hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span B q Ω[B⁄k] (span_range_derivation k B)
    have hz : z ∈ Submodule.span B
        (⇑(exteriorPower.ιMulti B q) '' {a | Set.range a ⊆ Set.range (D k B)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k B (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [hιD]
      exact ιMulti_D_mem_omB_regForms B q w
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul b z _ h => rw [map_smul, hB]; exact smul_mem_omB_regForms B q b.2 h

end GlobalTheory.PD
