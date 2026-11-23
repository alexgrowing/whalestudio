import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdaptedLatticeFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.SelfDualExtend

theorem exists_mem_hE_eq_of_integral :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ L₀ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L₀ → (∀ v, IsSelfDualAt σ J L₀ v) →
    ∀ (K : Submodule E (Fin n → E)) (y : Fin n → E), (∀ z ∈ L₀, z ∈ K → hE σ J z y ∈ (algebraMap (𝓞 E) E).range) →
        ∃ z ∈ L₀, ∀ x ∈ K, hE σ J x z = hE σ J x y := by
  intro F E _ _ _ _ _ σ n J hJ L₀ hL hsd K y hy
  classical
  set N : Submodule (𝓞 E) (Fin n → E) := L₀ ⊓ K.restrictScalars (𝓞 E) with hNdef
  have hsat : GlobalTheory.IsSaturatedIn L₀ N := GlobalTheory.isSaturatedIn_inf_restrictScalars L₀ K
  haveI : Module.Finite (𝓞 E) L₀ := Module.Finite.iff_fg.2 hL.fg
  obtain ⟨N', hdis, hsup⟩ := hsat.exists_disjoint_sup_eq
  set K' : Submodule E (Fin n → E) := Submodule.span E (N' : Set (Fin n → E)) with hK'def
  have hN'L : N' ≤ L₀ := hsup ▸ le_sup_right
  have hc : IsCompl K K' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvK hvK'
      have hv : v ∈ GlobalTheory.saturation N' := by
        rw [GlobalTheory.saturation_eq_span E]; exact hvK'
      obtain ⟨a, ha, hav⟩ := GlobalTheory.mem_saturation_iff.1 hv
      have h1 : a • v ∈ N := ⟨hN'L hav, K.smul_of_tower_mem a hvK⟩
      have h0 : a • v = 0 := (Submodule.disjoint_def.1 hdis) _ h1 hav
      rw [← algebraMap_smul E a v] at h0
      exact (smul_eq_zero.1 h0).resolve_left (by simpa using ha)
    · rw [codisjoint_iff, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
      intro z hz
      rw [← hsup] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
      exact Submodule.add_mem_sup ha.2 (Submodule.subset_span hb)
  let p : (Fin n → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ K.projectionOnto K' hc
  have hpK : ∀ x ∈ K, p x = x := fun x hx => by
    show ((K.projectionOnto K' hc x : K) : Fin n → E) = x
    rw [show x = ((⟨x, hx⟩ : K) : Fin n → E) from rfl, Submodule.projectionOnto_apply_left]
  have hpL : ∀ z ∈ L₀, p z ∈ L₀ ∧ p z ∈ K := by
    intro z hz
    rw [← hsup] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
    have hbK' : b ∈ K' := Submodule.subset_span hb
    have hb0 : p b = 0 := by
      show ((K.projectionOnto K' hc b : K) : Fin n → E) = 0
      rw [show b = ((⟨b, hbK'⟩ : K') : Fin n → E) from rfl, Submodule.projectionOnto_apply_right]
      rfl
    rw [map_add, hpK a ha.2, hb0, add_zero]
    exact ⟨ha.1, ha.2⟩
  set Pm := LinearMap.toMatrix' p with hPmdef
  have hPm : ∀ x, Pm *ᵥ x = p x := fun x => by simp [Pm, LinearMap.toMatrix'_mulVec]
  have hdetU : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hGQ : J * (J⁻¹ * (cT (σ : E →+* E) Pm * J)) = cT (σ : E →+* E) Pm * J := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetU, Matrix.one_mul]
  have key : ∀ x, hE σ J x ((J⁻¹ * (cT (σ : E →+* E) Pm * J)) *ᵥ y) = hE σ J (p x) y := fun x => by
    rw [← hPm, GlobalTheory.HypAdapt.hE_mulVec σ J hGQ]
  refine ⟨(J⁻¹ * (cT (σ : E →+* E) Pm * J)) *ᵥ y, ?_, fun x hx => by rw [key, hpK x hx]⟩
  refine ((GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJ hL).1 hsd _).2 fun x hx => ?_
  rw [key]
  exact hy _ (hpL x hx).1 (hpL x hx).2

end GlobalTheory.SelfDualExtend
