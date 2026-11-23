import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SerSys

theorem finTyp_eq_iSup_rt_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, ∃ b, NG.rt L n x (T a) = T b) → π.S = ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) := by
  intro L _ _ _ n π s V _ _ _ T hT hTS hx
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hone : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f := by
    intro f; funext g; simp [NG.rt]
  have h1 : TrivOutside {s.v}ᶜ (1 : GAf L n) := by
    intro v _; simp
  set Wd := ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) with hWd
  have hle : Wd ≤ π.S := by
    refine iSup_le fun y => ?_
    rintro f ⟨a, rfl⟩
    exact π.stable _ _ (hTS a)
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro y _ ⟨a, rfl⟩
      obtain ⟨x, y', hx1, hy', he⟩ := hdec (h * y.1)
      obtain ⟨b, hb⟩ := hx x hx1 a
      have : NG.rt L n h (NG.rt L n y.1 (T a)) = NG.rt L n y' (T b) := by
        rw [hrt, he, (hcomm x y' hx1 hy').eq, ← hrt, hb]
      simp only [LinearMap.comp_apply]
      rw [this]
      exact Submodule.mem_iSup_of_mem (⟨y', hy'⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) ⟨b, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  rcases π.irr Wd hle hstab with h0 | h0
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (0 : V)
    have hmem : T a ∈ Wd := by
      have := Submodule.mem_iSup_of_mem (p := fun y : {y : GAf L n // TrivOutside {s.v}ᶜ y} => LinearMap.range ((NG.rt L n y.1).comp T)) (⟨1, h1⟩ : {y : GAf L n // TrivOutside {s.v}ᶜ y}) (⟨a, rfl⟩ : ((NG.rt L n 1).comp T) a ∈ LinearMap.range ((NG.rt L n 1).comp T))
      simpa [hone] using this
    rw [h0, Submodule.mem_bot] at hmem
    exact ha (hT (by rw [hmem, map_zero]))
  · exact h0.symm

end GlobalTheory.SerSys
