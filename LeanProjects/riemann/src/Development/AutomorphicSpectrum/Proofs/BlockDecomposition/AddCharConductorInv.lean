import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphStd

theorem isTrivialOn_inv_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (n : ℤ) :
    IsTrivialOn ψ⁻¹ n ↔ IsTrivialOn ψ n := by
  constructor
  · intro h x hx
    have h1 := h (-x) (neg_mem hx)
    rwa [AddChar.inv_apply, neg_neg] at h1
  · intro h x hx
    rw [AddChar.inv_apply]
    exact h (-x) (neg_mem hx)

theorem addCharConductor_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) :
    addCharConductor ψ⁻¹ = addCharConductor ψ := by
  unfold addCharConductor
  congr 1
  ext n
  exact isTrivialOn_inv_iff ψ n

theorem isStd_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ψ : AddChar F Circle} (hψ : IsStd ψ) : IsStd ψ⁻¹ := by
  refine ⟨?_, inv_ne_one.2 hψ.2.1, ?_⟩
  · exact (hψ.1.comp continuous_neg).congr fun x => (AddChar.inv_apply ψ x).symm
  · rw [addCharConductor_inv]
    exact hψ.2.2

theorem isStd_psiF (v : Ad3.Pl) : Ad3.IsStd (Ad3.GP.psiF v) :=
  GlobalTheory.CompanionTheory.RankinQ.isStd_local v

theorem isStd_psiF_inv : ∀ v : Ad3.Pl, Ad3.IsStd (Ad3.GP.psiF v)⁻¹ :=
  fun v => isStd_inv (isStd_psiF v)

end GlobalTheory.CompanionTheory.SphStd
