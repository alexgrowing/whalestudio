import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem modu_eq_modu_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ u k hu hk
  obtain ⟨-, -, h2, hc⟩ := h
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hc, hc, star_star]
  have hss : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = _
      rw [hσ]
  let b : Module.Basis (Fin 2) R (R ⊗[F] E) :=
    Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)
  have hku : IsUnit k := by
    have h1 : IsUnit (algebraMap R (R ⊗[F] E) k) := by
      rw [hk]; exact hu.mul (hu.map _)
    have h3 := h1.map (Algebra.norm R)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h3
    exact (isUnit_pow_iff two_ne_zero).1 h3
  refine ⟨hku, ?_⟩
  letI : StarRing (R ⊗[F] E) :=
    { star := sigR R σ
      star_involutive := hss
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add _ x y }
  haveI : ContinuousStar (R ⊗[F] E) := ⟨GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ⟩
  rw [modu, modu, dif_pos hu, dif_pos hku]
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm R (R ⊗[F] E) b.equivFun.symm
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap) hu.unit hku.unit hk

end GlobalTheory.GaugeEx
