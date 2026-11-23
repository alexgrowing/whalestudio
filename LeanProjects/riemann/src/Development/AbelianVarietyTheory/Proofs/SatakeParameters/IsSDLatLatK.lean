import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

noncomputable section

namespace GlobalTheory.SDCompan

section Gen

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp Formalism.L2.KerInert
open scoped TensorProduct

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

theorem latAd_eq (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

theorem compan_zero (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J 0 Λ = Λ := by
  rw [compan_eq, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul, sup_bot_eq]

theorem mem_toStd (J : Matrix (Fin N) (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M ↔
      (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J x) = x :=
      LinearEquiv.symm_apply_apply _ x
    simpa using (this ▸ hx)
  · intro h
    exact ⟨_, h, by simp⟩

theorem isSD_toStd (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    {M : Submodule (𝓞 E) (Fin N → E)} (hM : IsLat M) (hsd : dl sp.cm.sig J M = M) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M) := by
  have hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J) :=
    Classical.epsilon_spec hco
  set co := Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J with hco_def
  have key : ∀ x y, stdH E N (co x) (co y) = hform (sp.cm.sig : E →+* E) J x y := fun x y => hc x y
  refine ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_, fun y => ?_⟩
  · rw [Formalism.L2.PairingIndexBounds.F.toStd, Submodule.map_coe, LinearMap.coe_restrictScalars, ← hco_def, eq_top_iff]
    rintro v -
    have hv : co.symm v ∈ Submodule.span E (M : Set (Fin N → E)) := by rw [hM.2]; trivial
    have h1 := Submodule.apply_mem_span_image_of_mem_span (co : (Fin N → E) →ₗ[E] (Fin N → E)) hv
    simpa using h1
  · rw [mem_toStd (sp := sp), ← hco_def]
    constructor
    · intro hy x hx
      rw [mem_toStd (sp := sp), ← hco_def] at hx
      have h1 := (mem_dl sp.cm.sig J M (co.symm y)).1 (hsd.symm ▸ hy) (co.symm x) hx
      rw [← key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      rw [← hsd, mem_dl]
      intro x hx
      have h1 := h (co x) ((mem_toStd (sp := sp) J M (co x)).2 (by rw [← hco_def, LinearEquiv.symm_apply_apply]; exact hx))
      rw [← LinearEquiv.apply_symm_apply co y, key] at h1
      exact h1

theorem isSD_core (J : Matrix (Fin N) (Fin N) E)
    (hJ : ∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M))
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    {Lb M0 : Submodule (𝓞 E) (Fin N → E)} (hLb : IsLat Lb) (a : 𝓞 E)
    (hA : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb = M0) (hM0 : IsLat M0) (hsd : dl sp.cm.sig J M0 = M0) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
      (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) := by
  have hG : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb) = Formalism.UG.CS.globLat y M0 := by
    rw [latAd_eq, ← hA]
    by_cases ha : a = 0
    · subst ha
      rw [compan_zero, compan_zero]
    · rw [compan_eq, compan_eq]
      exact (glob_companion sp.cm.sig J hJ hLb ha y hy).symm
  rw [hG]
  exact isSD_toStd (sp := sp) J hco (isLat_glob hM0 y) (glob_selfdual sp.cm.sig J hJ hM0 hsd y hy)

end Gen

section Main

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSDLat_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M)) → (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F), ∀ (Lb : Submodule (𝓞 E) (Fin N → E)) (a : 𝓞 E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (compan (sp := sp) J a Lb) → Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J (compan (sp := sp) J a Lb) = compan (sp := sp) J a Lb → IsSDLat E N (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N J hJ hco y hy Lb a hLb hM hsd
  exact isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM hsd

end Main

end GlobalTheory.SDCompan
