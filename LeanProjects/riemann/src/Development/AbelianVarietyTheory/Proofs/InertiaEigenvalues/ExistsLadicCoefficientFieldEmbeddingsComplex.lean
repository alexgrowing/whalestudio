import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EmbExt

open Cardinal

theorem exists_extend_of_countable {A K : Type} [Field A] [Field K] [Algebra A K] [Countable A]
    (hK : #K ≤ 𝔠) (φ : A →+* ℂ) : ∃ ψ : K →+* ℂ, ∀ a, ψ (algebraMap A K a) = φ a := by
  letI : Algebra A ℂ := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A ℂ
  have hA : #A ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have ht' : #ℂ = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hA hC
  have hst : #s ≤ #t := by
    rw [← ht', Cardinal.mk_complex]
    exact (Cardinal.mk_le_mk_of_subset (Set.subset_univ _)).trans (by simpa using hK)
  obtain ⟨f⟩ := hst
  have hw : AlgebraicIndependent A (fun x : s => ((f x : t) : ℂ)) :=
    ht.1.comp (fun x => f x) f.injective
  let S := Algebra.adjoin A (Set.range ((↑) : s → K))
  let g : S →ₐ[A] ℂ := (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := (show Function.Injective (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))) from hw).comp
    hs.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hg
  haveI : Module.IsTorsionFree S K := Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[S] ℂ := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, fun a => ?_⟩
  have h1 : algebraMap A K a = algebraMap S K (algebraMap A S a) := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, ψ.commutes]
  exact g.commutes a

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem isAlgebraic_rat_of_isIntegral_int {R F : Type} [CommRing R] [Field F] [CharZero F] (g : R →+* F)
    {y : R} (hy : IsIntegral ℤ y) : IsAlgebraic ℚ (g y) := by
  obtain ⟨p, hp, hev⟩ := hy
  refine ⟨p.map (Int.castRingHom ℚ), (hp.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have h : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = g.comp (algebraMap ℤ R) := RingHom.ext_int _ _
  rw [h, ← Polynomial.hom_eval₂, hev, map_zero]

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem exists_side_embeddings : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  intro D N X f0 hf0 hcard
  have hcz : ∀ i, CharZero (FractionRing (X.O0 i)) := fun i => charZero_of_injective_ringHom (X.emb0 i).injective
  have key : ∀ i b, ∃ e : FractionRing (X.O i) →+* ℂ, letI := hcz i; ∀ z : FractionRing (X.O0 i), IsAlgebraic ℚ z →
      e (IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i) z) = f0 i b z := by
    intro i b
    letI := hcz i
    let A := algebraicClosure ℚ (FractionRing (X.O0 i))
    haveI : Algebra.IsAlgebraic ℚ A := ⟨fun a => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 a.2)⟩
    haveI : Countable A := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ A).trans (by simp)
    let m := IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i)
    letI : Algebra A (FractionRing (X.O i)) := (m.comp (algebraMap A (FractionRing (X.O0 i)))).toAlgebra
    have hK : Cardinal.mk (FractionRing (X.O i)) ≤ Cardinal.continuum :=
      (Cardinal.mk_le_of_injective (IsFractionRing.map (A := X.O i) (B := X.Ok i 0) (K := FractionRing (X.O i))
        (L := FractionRing (X.Ok i 0)) (X.Ok_inj i 0)).injective).trans (hcard i 0)
    obtain ⟨ψ, hψ⟩ := exists_extend_of_countable hK ((f0 i b).comp (algebraMap A (FractionRing (X.O0 i))))
    refine ⟨ψ, fun z hz => ?_⟩
    have hzA : z ∈ A := mem_algebraicClosure_iff.2 hz
    exact hψ ⟨z, hzA⟩
  choose e he using key
  have keyk : ∀ i b k, ∃ ek : FractionRing (X.Ok i k) →+* ℂ, ∀ x : X.O i,
      ek (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) =
        e i b (algebraMap (X.O i) (FractionRing (X.O i)) x) := by
    intro i b k
    letI : Algebra (X.O i) ℂ := ((e i b).comp (algebraMap (X.O i) (FractionRing (X.O i)))).toAlgebra
    haveI : Module.IsTorsionFree (X.O i) ℂ := Module.isTorsionFree_iff_algebraMap_injective.2
      ((e i b).injective.comp (IsFractionRing.injective (X.O i) (FractionRing (X.O i))))
    haveI : Module.IsTorsionFree (X.O i) (FractionRing (X.Ok i k)) := by
      refine Module.isTorsionFree_iff_algebraMap_injective.2 ?_
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))]
      exact (IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (X.Ok_inj i k)
    haveI := X.Ok_fin i k
    haveI : Algebra.IsAlgebraic (X.O i) (X.Ok i k) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsAlgebraic (X.O i) (FractionRing (X.Ok i k)) :=
      (IsFractionRing.isAlgebraic_iff' (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))).1 inferInstance
    let ψ : FractionRing (X.Ok i k) →ₐ[X.O i] ℂ := IsAlgClosed.lift
    refine ⟨ψ.toRingHom, fun x => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← IsScalarTower.algebraMap_apply, ψ.commutes]
    rfl
  choose ek hek using keyk
  refine ⟨e, ek, fun i b x => ?_, hek, fun i b y hy => ?_⟩
  · letI := hcz i
    have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 : IsAlgebraic ℚ ((if b then X.emb0 i else X.emb0b i) x) :=
      hx.algHom ((if b then X.emb0 i else X.emb0b i).toRatAlgHom)
    rw [← hf0 i b x, ← he i b _ h2]
    rfl
  · letI := hcz i
    have h2 : IsAlgebraic ℚ (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y) :=
      isAlgebraic_rat_of_isIntegral_int _ hy
    rw [← he i b _ h2]
    simp [IsFractionRing.map, IsLocalization.map_eq]

end GlobalTheory.EmbExt
