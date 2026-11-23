import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalKTypeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.TypeSpace

section Abstract

variable {K X : Type*} [Group K] [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def restrictRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) :
    Representation ℂ K Y where
  toFun g := ((π g : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem span_orbit_stable' (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k : K => π k F),
      π g v ∈ Submodule.span ℂ (Set.range fun k : K => π k F) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end Abstract

theorem exists_typeSpace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  intro E _ _ _ a μ _ _ H hH hI F hFH hK
  obtain ⟨hSo, hfd⟩ := hK
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a

  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | R (latticeGL E a) μ (finGL E a k) F = F}
      mul_mem' := fun {x y} hx hy => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        have hy' : R (latticeGL E a) μ (finGL E a y) F = F := hy
        change R (latticeGL E a) μ (finGL E a (x * y)) F = F
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hy', hx']
      one_mem' := by
        change R (latticeGL E a) μ (finGL E a 1) F = F
        simp
      inv_mem' := fun {x} hx => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        change R (latticeGL E a) μ (finGL E a x⁻¹) F = F
        conv_lhs => rw [← hx']
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
        simp }
  have hSo' : IsOpen (S : Set (GL (Fin a) (Af E))) := hSo
  let U : Subgroup (GL (Fin a) (Af E)) := K0 ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hK0o.inter hSo'
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hK0c.inter_right (S.isClosed_of_isOpen hSo')

  let π : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
    (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)
  have hcomm : ∀ (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ),
      R (latticeGL E a) μ (finGL E a u) (π k v) = π k (R (latticeGL E a) μ (finGL E a u) v) := by
    intro u k v
    have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
    simp only [map_mul, ContinuousLinearMap.mul_apply] at e
    exact e.symm
  let Y : Submodule ℂ (L2 (latticeGL E a) μ) := Submodule.span ℂ (Set.range fun k : Kinf E a => π k F)
  haveI : FiniteDimensional ℂ Y := hfd
  have hYs : ∀ g, ∀ v ∈ Y, π g v ∈ Y := span_orbit_stable' π F
  have hFY : F ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hYP : ∀ v ∈ Y, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨hI.1.2 _ _ hFH, fun u hu => ?_⟩
      exact (hcomm u k F).trans (congrArg (π k) hu.2)
    | zero => exact ⟨H.zero_mem, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
    | smul c x _ hx =>
      exact ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩
  let ρ : Representation ℂ (Kinf E a) Y := restrictRep π Y hYs
  let C : (Y →ₗ[ℂ] L2 (latticeGL E a) μ) → Prop := fun T =>
    (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧
      ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w
  let X : Submodule ℂ (L2 (latticeGL E a) μ) := ⨆ (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T), LinearMap.range T
  have hXf : FiniteDimensional ℂ X := GlobalTheory.T.cuspidal_K_type_finite E a μ H hH hI U hUo Y ρ
  have hmem : ∀ T, C T → ∀ w, T w ∈ X := fun T hT w =>
    (le_iSup₂_of_le (f := fun (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T) => LinearMap.range T) T hT le_rfl)
      ⟨w, rfl⟩
  have hXP : ∀ v ∈ X, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    let P : Submodule ℂ (L2 (latticeGL E a) μ) :=
      { carrier := {v | v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
        zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
        add_mem' := fun {x y} hx hy =>
          ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
        smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
    have hle : X ≤ P := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      exact hT.2 w
    exact hle hv
  refine ⟨U, hUo, hUc, X, hXf, ?_, fun v hv => (hXP v hv).1, ?_, fun u hu v hv => (hXP v hv).2 u hu, ?_⟩
  · exact hmem Y.subtype ⟨fun k w => rfl, fun w => hYP _ w.2⟩ ⟨F, hFY⟩
  · intro k v hv
    have hle : X ≤ X.comap ((R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) :
        L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
      iSup₂_le fun T hT => by
        rintro _ ⟨w, rfl⟩
        change R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w) ∈ X
        rw [← hT.1 k w]
        exact hmem T hT _
    exact hle hv
  · intro B hB1 hB2 v hv
    have hle : X ≤ X.comap B := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine hmem (B ∘ₗ T) ⟨fun k w => ?_, fun w => hB2 _ (hT.2 w).1 (hT.2 w).2⟩ w
      change B (T (ρ k w)) = _
      rw [hT.1 k w, hB1]
      rfl
    exact hle hv

end GlobalTheory.CompanionTheory.TypeSpace

end
