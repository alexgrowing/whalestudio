import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.EqRed
open GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem eq_zero_of_forall_mem_map (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (x : A)
    (h : ∀ e : ℕ, x ∈ (I ^ (e + 1)).map (algebraMap R A)) : x = 0 := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := A) I hI
  have hx : x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule R A)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have h1 : x ∈ (I ^ (i + 1) • (⊤ : Submodule R A)) := by
      rw [Ideal.smul_top_eq_map]
      exact h i
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h1
  rw [key] at hx
  simpa using hx

theorem eq_of_reductions (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) : f = g := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom

  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  have : Module.Finite R Γ(X.left, ⊤) := hfin'

  let u : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom
  let v : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ g.left ≫ Y.left.isoSpec.hom
  have hu : Spec.map (Spec.preimage u) = u := Spec.map_preimage _
  have hv : Spec.map (Spec.preimage v) = v := Spec.map_preimage _

  have hred : ∀ e : ℕ, Spec.preimage u ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) = Spec.preimage v ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) := by
    intro e
    let J := (I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤))
    let m : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec Γ(X.left, ⊤) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let q : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap R Γ(X.left, ⊤)) Ideal.le_comap_map))
    have hcond : (m ≫ X.left.isoSpec.inv) ≫ X.hom = q ≫ thick R I e := by
      rw [Category.assoc, ← hψ]
      simp only [m, q, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
    let t : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ (thickObj R I e X).left :=
      pullback.lift (m ≫ X.left.isoSpec.inv) q hcond
    have ht : t ≫ thickι I e X = m ≫ X.left.isoSpec.inv := pullback.lift_fst _ _ _
    have hfg : thickι I e X ≫ f.left = thickι I e X ≫ g.left := by
      have hl : thickHom I e f = thickHom I e g := congrArg (fun φ => φ.left) (h e)
      rw [← thickHom_ι, ← thickHom_ι, hl]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hu, hv]
    change m ≫ u = m ≫ v
    simp only [u, v]
    rw [← Category.assoc m, ← Category.assoc m, ← ht, Category.assoc t, Category.assoc t,
      reassoc_of% hfg]
  have hpre : Spec.preimage u = Spec.preimage v := by
    ext b
    refine sub_eq_zero.1 (eq_zero_of_forall_mem_map I Γ(X.left, ⊤) _ fun e => ?_)
    exact Ideal.Quotient.eq.1 (congrArg (fun φ => φ.hom b) (hred e))
  have huv : u = v := by rw [← hu, ← hv, hpre]
  apply Over.OverMorphism.ext
  have h1 : f.left ≫ Y.left.isoSpec.hom = g.left ≫ Y.left.isoSpec.hom := (cancel_epi X.left.isoSpec.inv).1 huv
  exact (cancel_mono Y.left.isoSpec.hom).1 h1

end GlobalTheory.CompanionTheory.Ar.BT.EqRed
