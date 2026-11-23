import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import GroundTheory.AutomorphicForms.Satake
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeriesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBoundStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_principalSeriesSpace_of_indSp {n : ℕ} (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n))
      ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)) :
    (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) :=
  GlobalTheory.T.induced_in_principal_series k n α f

theorem isSatakeParameter_of_isSubquotient_of_injective {n : ℕ} (α : Fin n → ℂˣ) {X V : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) k) X}
    (hρ : IsSmooth ρ) (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))) (hι : Function.Injective ι)
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π ρ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  GlobalTheory.T.subquotient_principal_series_bound k n α X V ρ hρ ι hι π h μ

theorem KO_eq_integralGL (n : ℕ) : KO k (Fin n) = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := by
  ext v
  simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]

def bridge {n : ℕ} (α : Fin n → ℂˣ) :
    (prinSeries fun i => unrChar k (α i)).IntertwiningMap (principalSeries k n (paramChar k α)) where
  toFun f := ⟨fun g => f.1.1 g, mem_principalSeriesSpace_of_indSp α f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl)

theorem bridge_injective {n : ℕ} (α : Fin n → ℂˣ) : Function.Injective (bridge (k := k) α) := fun f f' e =>
  by
  have := congrArg Subtype.val e
  apply Subtype.ext
  apply Subtype.ext
  exact this

theorem isSatakeParameter_of_isSubquotient {n : ℕ} (α : Fin n → ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π (prinSeries fun i => unrChar k (α i)))
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  isSatakeParameter_of_isSubquotient_of_injective α (isSmooth_parInd _ _) (bridge α) (bridge_injective α) h μ

theorem hasSupport_prinSeries (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (π : IrrRep (GL (Fin n) k)) (h : IsSubquotient π.ρ (prinSeries χ)) :
    HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  have H : GlobalTheory.SmGL.IsCuspSupport π.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨π.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.CompanionTheory.SphSupp

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpherical_iff_fixedVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) :
    IsSpherical π ↔ GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.integralGL k n) ≠ ⊥ := by
  show fixed π (KO k (Fin n)) ≠ ⊥ ↔ _
  rw [KO_eq_integralGL, fixed_eq_fixedVectors]

end GlobalTheory.CompanionTheory.SphSupp
