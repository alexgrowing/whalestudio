import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistChoiceExample
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField

namespace GlobalTheory.DualFinitelyGenerated

variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

theorem hform_single_apply (H : Matrix (Fin d) (Fin d) K) (i : Fin d) (x : Fin d → K) :
    Formalism.DivisionValues.hform H (Pi.single i 1) x = (H.mulVec x) i := by
  simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem dual_fg (H : Matrix (Fin d) (Fin d) K) (hH : H.det ≠ 0)
    (T : Submodule (𝓞 K) (Fin d → K)) (hT : Submodule.IsLattice K T) :
    (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T).FG := by
  obtain ⟨s, hs⟩ := hT.fg
  let φ : (Fin d → K) →ₗ[𝓞 K] (s → K) :=
    (LinearMap.pi fun t : s => Formalism.DivisionValues.hform H t.1).restrictScalars (𝓞 K)
  let ψ : (s → 𝓞 K) →ₗ[𝓞 K] (s → K) :=
    LinearMap.pi fun t : s => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj t)
  have hspan : Submodule.span K (s : Set (Fin d → K)) = ⊤ := by
    have := hT.span_eq_top
    rw [← hs, Submodule.span_span_of_tower] at this
    exact this
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : ∀ t ∈ s, Formalism.DivisionValues.hform H t x = 0 := fun t ht => congrFun hx ⟨t, ht⟩
    have hle : Submodule.span K (s : Set (Fin d → K)) ≤ LinearMap.ker ((Formalism.DivisionValues.hform H).flip x) := by
      rw [Submodule.span_le]
      intro t ht
      simpa using h0 t ht
    rw [hspan] at hle
    have hv : H.mulVec x = 0 := by
      funext i
      rw [← hform_single_apply]
      have := hle (Submodule.mem_top (x := Pi.single i 1))
      simpa using this
    simpa using Matrix.eq_zero_of_mulVec_eq_zero hH hv
  have hψ : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have hle : (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hx
    have hr : ∀ t : s, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = Formalism.DivisionValues.hform H t.1 x := by
      intro t
      have := hx t.1 (hs ▸ Submodule.subset_span t.2)
      rw [Submodule.mem_one] at this
      exact this
    choose r hr using hr
    refine ⟨r, ?_⟩
    funext t
    simp [ψ, φ, hr t]
  haveI : IsNoetherian (𝓞 K) (LinearMap.range ψ) := isNoetherian_of_fg_of_noetherian _ hψ
  exact Submodule.fg_of_fg_map_injective φ hinj (Submodule.FG.of_le_of_isNoetherian hle)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : StarRing K] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) K), Matrix.det H ≠ (0 : K) →
    ∀ (T : Submodule (NumberField.RingOfIntegers K) (Fin d → K)), Submodule.IsLattice K T →
      Submodule.FG (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) T) :=
  fun H hH T hT => dual_fg H hH T hT

end GlobalTheory.DualFinitelyGenerated
