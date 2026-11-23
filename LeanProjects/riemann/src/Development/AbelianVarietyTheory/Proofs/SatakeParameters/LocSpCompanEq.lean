import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.CompSp

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.TwV.CompSp.locSp_compan_eq : ∀ {R : _root_.Formalism.BasicNotions.Ranks} {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : _root_.Formalism.BasicNotions.Spaces R F E)
    (W K : Type) [CommRing W] [Field K] [Algebra W K] (ρ : E →+* K) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)),
    IsUnit (T : W) → (∀ z ∈ _root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ, (T : E) • z ∈ Λ) →
      _root_.GlobalTheory.TwV.locSp W ρ (_root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ) =
        _root_.GlobalTheory.TwV.locSp W ρ Λ := by
  intro R F E _ _ _ _ _ _ sp W K _ _ _ ρ N J a T Λ hT hdual
  have hsub : Λ ≤ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ := by
    simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
    exact le_sup_left
  have key : ∀ x ∈ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ, T • x ∈ Λ := by
    intro x hx
    let S : Submodule (𝓞 E) (Fin N → E) :=
      Λ.comap (T • LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
    have hΛS : Λ ≤ S := fun y hy => by
      simp only [S, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      exact nsmul_mem hy T
    have hDS : Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ) ≤ S := by
      rw [Submodule.span_le]
      intro z hz
      simp only [S, SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply]
      simpa [Nat.cast_smul_eq_nsmul] using hdual z hz
    have hle : _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ ≤ S := by
      simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
      exact sup_le hΛS (Submodule.smul_le_right.trans hDS)
    have := hle hx
    simpa [S] using this
  simp only [_root_.GlobalTheory.TwV.locSp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := hT
    have h1 : (fun k => ρ ((T • x) k)) ∈
        Submodule.span W ((fun x k ↦ ρ (x k)) '' (Λ : Set (Fin N → E))) :=
      Submodule.subset_span ⟨_, key x hx, rfl⟩
    have h2 : (fun k => ρ ((T • x) k)) = (u : W) • (fun k => ρ (x k)) := by
      funext k
      simp [hu, map_nsmul, Nat.cast_smul_eq_nsmul]
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Wˣ) : W) h1
    rwa [h2, smul_smul, Units.inv_mul, one_smul] at h3
  · exact Submodule.span_mono (Set.image_mono hsub)

end GlobalTheory.TwV.CompSp
