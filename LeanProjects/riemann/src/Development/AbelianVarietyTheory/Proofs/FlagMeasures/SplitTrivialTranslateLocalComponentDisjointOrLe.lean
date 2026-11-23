import Mathlib
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

theorem GlobalTheory.SlocDich.translate_dichotomy : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  intro L _ _ _ n s τ i T _hTi hT y hy P hP
  have hpart := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s

  have hstab : ∀ (g : GL (Fin n) (s.w.adicCompletion L)) (a : τ.V),
      a ∈ P.comap ((NG.rt L n y).comp T) → τ.ρ g a ∈ P.comap ((NG.rt L n y).comp T) := by
    intro g a ha
    obtain ⟨x, ⟨hx, hxA⟩, -⟩ := hpart.2.2 (Matrix.GeneralLinearGroup.map i.symm.toRingHom g)
    have hg : g = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) := by
      rw [hxA]; ext j k; simp
    have hc := hpart.2.1 x y hx hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply] at ha ⊢
    rw [hg, hT x hx a]
    have e : NG.rt L n y (NG.rt L n x (T a)) = NG.rt L n x (NG.rt L n y (T a)) := by
      funext g'
      show T a (g' * y * x) = T a (g' * x * y)
      rw [mul_assoc, mul_assoc, hc.eq]
    rw [e]
    exact hP x hx _ ha
  let Q : Subrepresentation τ.ρ := ⟨P.comap ((NG.rt L n y).comp T), hstab⟩
  rcases τ.irr.eq_bot_or_eq_top Q with h | h
  · left
    rw [Submodule.disjoint_def]
    rintro f ⟨a, rfl⟩ hf
    have ha : a ∈ Q.toSubmodule := hf
    rw [h] at ha
    have : a = 0 := ha
    simp [this]
  · right
    rintro f ⟨a, rfl⟩
    have ha : a ∈ Q.toSubmodule := by rw [h]; trivial
    exact ha
