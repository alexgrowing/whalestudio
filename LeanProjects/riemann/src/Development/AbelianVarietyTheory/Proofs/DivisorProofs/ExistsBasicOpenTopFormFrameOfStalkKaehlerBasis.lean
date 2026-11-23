import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.FrameSpread

open GlobalTheory.TopForm

theorem exists_basicOpen_isFrame_dOn : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  intro k _ X p n _ U x₀ hx x hbs
  obtain ⟨V, ω, hxV, hω⟩ := TopForm.exists_isFrame p n x₀
  obtain ⟨s, hsV, hxs⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hx
  have hWU : X.basicOpen s ≤ U.1 := X.basicOpen_le s
  have hWaff : IsAffineOpen (X.basicOpen s) := U.2.basicOpen s
  have hωW := hω.res hWaff hsV
  set η : FormsOn p n (X.basicOpen s) := TopForm.dOn p (fun i => resG X hWU (x i)) with hη
  set J : Γ(X, X.basicOpen s) := hωW.gen.repr η with hJdef
  have hJ : J • TopForm.resForm hsV ω = η := hωW.gen.repr_smul η
  obtain ⟨bs, hbs⟩ := hbs
  set ρ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk x₀ := (X.presheaf.germ (X.basicOpen s) x₀ hxs).hom with hρ
  have hgerm : ∀ a : Γ(X, U.1), ρ (resG X hWU a) = (X.presheaf.germ U.1 x₀ hx).hom a := fun a => by
    have := TopCat.Presheaf.germ_res X.presheaf (homOfLE hWU) x₀ hxs
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) this
  have hρα : ρ.comp (algX p (X.basicOpen s)) = (X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1) := by
    rw [← resG_comp_algX p hWU]
    ext a
    exact hgerm _
  have hfe : letI := ρ.toAlgebra; Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := by
    letI := ρ.toAlgebra
    haveI := hWaff.isLocalization_stalk ⟨x₀, hxs⟩
    exact Algebra.FormallyEtale.of_isLocalization (hWaff.primeIdealOf ⟨x₀, hxs⟩).asIdeal.primeCompl
  have h1 : IsFreeGen (X.presheaf.stalk x₀) (TopForm.formMap n ρ hρα (TopForm.resForm hsV ω)) := by
    letI := (algX p (X.basicOpen s)).toAlgebra
    letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra
    letI := ρ.toAlgebra
    haveI : IsScalarTower k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) :=
      IsScalarTower.of_algebraMap_eq' hρα.symm
    haveI : Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := hfe
    exact hωW.gen.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀)) n)
  have h2 : IsFreeGen (X.presheaf.stalk x₀)
      (dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
        (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i))) :=
    isFreeGen_dForm _ bs hbs
  have h3 : TopForm.formMap n ρ hρα η = ρ J • TopForm.formMap n ρ hρα (TopForm.resForm hsV ω) := by
    rw [← hJ, map_smulₛₗ]
  have h4 : TopForm.formMap n ρ hρα η = dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
      (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i)) := by
    rw [hη, dOn, formMap_dForm]
    simp only [hgerm]
  have hu : IsUnit (ρ J) := h1.smul_iff.1 (h3 ▸ h4 ▸ h2)
  have hxJ : x₀ ∈ X.basicOpen J := (X.mem_basicOpen J x₀ hxs).2 hu
  obtain ⟨t, htJ, hxt⟩ := U.2.exists_basicOpen_le ⟨x₀, hxJ⟩ hx
  refine ⟨t, hxt, ?_⟩
  have hJW : X.basicOpen J ≤ X.basicOpen s := X.basicOpen_le J
  have hte : X.basicOpen t ≤ X.basicOpen s := htJ.trans hJW
  have hframe := hωW.res (U.2.basicOpen t) hte
  have e : TopForm.dOn p (fun i => resG X (X.basicOpen_le t) (x i)) =
      resG X hte J • TopForm.resForm hte (TopForm.resForm hsV ω) := by
    rw [← resForm_smul, hJ, hη, resForm_dOn]
    simp only [resG_resG]
  rw [e]
  refine ⟨U.2.basicOpen t, hframe.gen.smul_iff.2 ?_⟩
  have hu' : IsUnit (resG X hJW J) := X.toRingedSpace.isUnit_res_basicOpen J
  have := hu'.map (resG X htJ)
  rwa [resG_resG] at this

end GlobalTheory.FrameSpread
