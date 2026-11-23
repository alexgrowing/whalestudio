import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreeOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_affine_nbhd_detGen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
    ∃ (W : M.Opens) (hW : IsAffineOpen W), y ∈ W ∧ ∃ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ ∧ Nonempty Y.DetGen := by
  intro F _ _ 𝔠 M U y
  obtain ⟨W₀, hW₀, hyW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens) (show y ∈ (⊤ : M.Opens) from trivial)
  have hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y₀, φ₀, h₀⟩ := exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y₀
  let q := hW₀.primeIdealOf ⟨y, hyW₀⟩
  let p : Ideal Γ(M, W₀) := q.asIdeal
  haveI : p.IsPrime := q.isPrime
  haveI : Module.FinitePresentation Γ(M, W₀) Y₀.Lie := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Y₀.Lie) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hg, hfree, hfr⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl Y₀.Lie) (Localization.AtPrime p)
  have hyW : y ∈ M.basicOpen g := by
    have h1 : q ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec q ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  have hW : IsAffineOpen (M.basicOpen g) := hW₀.basicOpen g
  letI : Algebra Γ(M, W₀) Γ(M, M.basicOpen g) := (M.presheaf.map (homOfLE (M.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g Γ(M, M.basicOpen g) := hW₀.isLocalization_basicOpen g
  obtain ⟨Y, ψ, hψ⟩ := exists_isPullBy (S' := Sp Γ(M, M.basicOpen g)) Y₀
    (spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)))
  have hcomp : spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)) ≫ hW₀.fromSpec = hW.fromSpec :=
    hW₀.map_fromSpec hW (homOfLE (M.basicOpen_le g)).op
  refine ⟨M.basicOpen g, hW, hyW, Y, ψ ≫ φ₀, by rw [← hcomp]; exact hψ.comp h₀, ?_⟩
  obtain ⟨e, -, -⟩ := exists_lieEquiv (R' := Γ(M, M.basicOpen g)) hψ
  haveI : Module.Finite (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie)
  have hd : Module.finrank (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) = Module.finrank ℚ F := by
    rw [hfr]
    exact hrk q
  haveI : Nontrivial (Localization.Away g) :=
    (IsLocalization.Away.lift g (S := Localization.Away g) (g := algebraMap Γ(M, W₀) (Localization.AtPrime p))
      (IsLocalization.map_units (Localization.AtPrime p) ⟨g, hg⟩)).domain_nontrivial
  let b₀ := Module.finBasisOfFinrankEq (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) hd
  haveI : IsLocalizedModule (Submonoid.powers g)
      (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Γ(M, M.basicOpen g) _).2
      (TensorProduct.isBaseChange _ _ _)
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie) (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(M, M.basicOpen g)
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars Γ(M, W₀) ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) Γ(M, M.basicOpen g)
  exact ⟨DetGen.ofBasis Y ((Module.Basis.ofRepr Ψ').map e)⟩

end GlobalTheory.RealMult.Obj
