import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RealMult.LocalGen

theorem exists_basis_away {A : Type} [CommRing A] (L : Type) [AddCommGroup L] [Module A L] [Module.Finite A L]
    [Module.Projective A L] (p : PrimeSpectrum A) (n : ℕ) (hn : Module.rankAtStalk (R := A) L p = n) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] [Algebra A B], IsUnit (algebraMap A B g) →
      Nonempty (Module.Basis (Fin n) B (B ⊗[A] L)) := by
  haveI : Module.FinitePresentation A L := Module.finitePresentation_of_projective A L
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Fin n) (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.finBasisOfFinrankEq _ _ hn
  obtain ⟨g, hg, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl L) (Localization.AtPrime p.asIdeal) b
  refine ⟨g, hg, fun B _ _ hu ↦ ?_⟩
  letI : Algebra (Localization (Submonoid.powers g)) B := (IsLocalization.Away.lift g hu).toAlgebra
  haveI : IsScalarTower A (Localization (Submonoid.powers g)) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq g hu a).symm
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization (Submonoid.powers g))
    (LocalizedModule.mkLinearMap (Submonoid.powers g) L)).equiv
  exact ⟨((b'.map e.symm).baseChange B).map
    (AlgebraTensorModule.cancelBaseChange A (Localization (Submonoid.powers g)) B B L)⟩

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem nonempty_detGen_of_basis {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))
    (b : Module.Basis (Fin (Module.finrank ℚ F)) R X.Lie) : Nonempty X.DetGen := by
  refine ⟨⟨b.det, Submodule.eq_top_iff'.2 fun f ↦ ?_⟩⟩
  rw [f.eq_smul_basis_det b]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_detGen_away {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (p : PrimeSpectrum A) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] (σ : A →+* B), IsUnit (σ g) →
      ∀ (X : Obj F 𝔠 (Sp B)) (φ : X.A.left ⟶ Y.A.left), X.IsPullBy Y (spMap σ) φ → Nonempty X.DetGen := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y
  obtain ⟨g, hg, H⟩ := exists_basis_away Y.Lie p _ (hrk p)
  refine ⟨g, hg, fun B _ σ hu X φ h ↦ ?_⟩
  letI := σ.toAlgebra
  obtain ⟨b⟩ := H B hu
  obtain ⟨e, -⟩ := Obj.exists_lieEquiv (R' := B) h
  exact nonempty_detGen_of_basis X (b.map e)

theorem exists_affine_detGen (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M) : ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hm, -⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ m) isOpen_univ
  replace hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y, ψ, hY⟩ := Obj.exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨g, hg, H⟩ := exists_detGen_away Y (hW₀.primeIdealOf ⟨m, hm⟩)
  refine ⟨M.basicOpen g, hW₀.basicOpen g, ?_, fun X φ h ↦ ?_⟩
  · have h1 : hW₀.primeIdealOf ⟨m, hm⟩ ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec (hW₀.primeIdealOf ⟨m, hm⟩) ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  · let ρ : Γ(M, W₀) ⟶ Γ(M, M.basicOpen g) := M.presheaf.map (homOfLE (M.basicOpen_le g)).op
    let j := (Algebra.TensorProduct.includeRight :
      Γ(M, M.basicOpen g) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, M.basicOpen g)).toRingHom
    have e : coefSpecMap (hW₀.basicOpen g) R₀ = spMap (j.comp ρ.hom) ≫ hW₀.fromSpec := by
      rw [coefSpecMap, ← hW₀.map_fromSpec (hW₀.basicOpen g) (homOfLE (M.basicOpen_le g)).op, ← Category.assoc]
      congr 1
      exact (Spec.map_comp ρ (CommRingCat.ofHom j)).symm
    rw [e] at h
    obtain ⟨χ, hχ, -⟩ := h.cancel hY
    exact H _ (j.comp ρ.hom) ((M.toRingedSpace.isUnit_res_basicOpen g).map j) X χ hχ

end GlobalTheory.RealMult.LocalGen
