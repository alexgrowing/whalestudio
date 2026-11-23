import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

namespace GlobalTheory.VB

theorem nonempty_basis_of_localizedModule {R M N ι : Type*} (B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module B N]
    [IsScalarTower R B N] (S : Submonoid R) [IsLocalization S B] (f : M →ₗ[R] N)
    [IsLocalizedModule S f] (b : Module.Basis ι (Localization S) (LocalizedModule S M)) :
    Nonempty (Module.Basis ι B N) := by
  let e : Localization S ≃ₐ[R] B := IsLocalization.algEquiv S _ _
  let : Module (Localization S) N := Module.compHom N e.toRingEquiv.toRingHom
  have hs (a : Localization S) (n : N) : a • n = e a • n := rfl
  have : IsScalarTower R (Localization S) N := ⟨fun r a n => by
    rw [hs, hs, map_smul, smul_assoc]⟩
  let φ := (IsLocalizedModule.iso S f).extendScalarsOfIsLocalization S (Localization S)
  exact ⟨(b.map φ).mapCoeffs e.toRingEquiv fun _ _ => rfl⟩

theorem isFrame_of_basis_affine {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(F, U)) : IsFrame (F := F) (U := U) b := by
  refine isFrame_of_forall_exists fun V h y hy => ?_
  obtain ⟨W, hW, hyW, hle⟩ := QCoh.exists_affine_mem_le y hy
  refine ⟨W, hle, hyW, ?_⟩
  let := QCoh.resAlgebra (hle.trans h)
  let := QCoh.resModule F (hle.trans h)
  have := QCoh.res_isScalarTower F (hle.trans h)
  let c := (QCoh.isBaseChange_resLinear F hU hW (hle.trans h)).basis b
  have hc (i : ι) : c i = Twist.resM F (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => Twist.resM F (hle.trans h) (b i)) =
      c.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hc]
  rw [this]
  exact c.equivFun.symm.bijective

theorem isVB_of_basis_stalk (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules)
    [GlobalTheory.QCoh.IsFiniteQC F] (r : ℕ)
    (h : ∀ x : X, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :))) :
    IsVB F r := by
  intro x
  obtain ⟨U, hU, hx, -⟩ := QCoh.exists_affine_mem_le (U := ⊤) x trivial
  obtain ⟨y, rfl⟩ : ∃ y : U, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨b⟩ := h y
  have := QCoh.finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.FinitePresentation Γ(X, U) Γ(F, U) := Module.finitePresentation_of_finite _ _
  have := QCoh.isLocalizedModule_germLinear F hU y
  have := hU.isLocalization_stalk y
  obtain ⟨f, hf, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear F y) (X.presheaf.stalk (y : X)) b
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen F hU f
  obtain ⟨c⟩ := nonempty_basis_of_localizedModule Γ(X, X.basicOpen f) (.powers f)
    (QCoh.resBasicOpen F f) b'
  exact ⟨X.basicOpen f, c, (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf,
    isFrame_of_basis_affine (hU.basicOpen f) c⟩

end GlobalTheory.VB
