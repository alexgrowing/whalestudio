import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R']
    [Algebra R R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R')) :
    ∃ L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
      ∃ j : R' →ₐ[R] L, Function.Injective j := by
  first
  | exact @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | (apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding ..)

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem isGal_integralClosure_of_tower (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (L : Type) [Field L]
    [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L] [IsGalois (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] :
    IsGal (algebraMap R (integralClosure R L)) := by
  set K := FractionRing R
  set B := integralClosure R L
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hRL : ∀ r : R, algebraMap B L (algebraMap R B r) = algebraMap K L (algebraMap R K r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply R K L]; rfl
  have hfix : ∀ τ : Gal (algebraMap R B), ∀ k : K,
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1 (algebraMap K L k) = algebraMap K L k := by
    intro τ k
    have h := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := K)
      (j := (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1).toRingHom.comp (algebraMap K L))
      (k := algebraMap K L) (by
        ext r
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hRL, IsFractionRing.ringEquivOfRingEquiv_algebraMap, τ.2 r])
    exact congrArg (fun f => f k) h
  let toAut : Gal (algebraMap R B) → (L ≃ₐ[K] L) := fun τ => AlgEquiv.ofRingEquiv (hfix τ)
  have htoAut : ∀ τ b, toAut τ (algebraMap B L b) = algebraMap B L (τ.1 b) := fun τ b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  refine ⟨Finite.of_injective toAut fun τ τ' h => Subtype.ext (RingEquiv.ext fun b => ?_), fun x hx => ?_⟩
  · apply IsFractionRing.injective B L
    rw [← htoAut, ← htoAut, h]
  · have hg : ∀ g : L ≃ₐ[K] L, g (x : L) = x := by
      intro g
      let gR : L →ₐ[R] L := (g : L →ₐ[K] L).restrictScalars R
      let gR' : L →ₐ[R] L := (g.symm : L →ₐ[K] L).restrictScalars R
      let τ : B ≃+* B :=
        { toFun := fun b => ⟨g b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR)⟩
          invFun := fun b => ⟨g.symm b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR')⟩
          left_inv := fun b => Subtype.ext (g.symm_apply_apply (b : L))
          right_inv := fun b => Subtype.ext (g.apply_symm_apply (b : L))
          map_mul' := fun a b => Subtype.ext (map_mul g (a : L) b)
          map_add' := fun a b => Subtype.ext (map_add g (a : L) b) }
      have hτ : τ ∈ Gal (algebraMap R B) := fun r => Subtype.ext (by
        show g ((algebraMap R B r : B) : L) = ((algebraMap R B r : B) : L)
        have e : ((algebraMap R B r : B) : L) = algebraMap K L (algebraMap R K r) := hRL r
        rw [e, AlgEquiv.commutes])
      exact congrArg Subtype.val (hx τ hτ)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (F := K) (x : L)).2 hg)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K L k) := hk ▸ (x.2 : IsIntegral R (x : L))
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    have := hRL r
    rw [hr, hk] at this
    exact this

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem exists_galois_finExt_isLocalHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'')
    (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  intro R R' _ _ _ _ _ _ ρ hR hρ
  obtain ⟨⟨hRn, -, hRic, hRc⟩, hR0⟩ := hR
  obtain ⟨-, hinj, hfin⟩ := hρ
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  obtain ⟨L, hLf, hLg, j, hj⟩ := exists_galois_embedding R R' hinj
  set B := integralClosure R L
  obtain ⟨hBfin, hBloc, hBn, hBic, -⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hRc L
  have hmem : ∀ x : R', j x ∈ B := fun x => (Algebra.IsIntegral.isIntegral (R := R) x).map j
  let jB : R' →ₐ[R] B := j.codRestrict B hmem
  let σ : R' →+* B := jB.toRingHom
  have hcomp : σ.comp ρ = algebraMap R B := RingHom.ext fun r => jB.commutes r
  have hadm : AdmBase B (maximalIdeal B) :=
    ⟨hBn, inferInstance, hBic, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R B⟩
  have hσinj : Function.Injective σ := fun a b h => hj (congrArg (fun y : B => (y : L)) h)
  have hcfin : (σ.comp ρ).Finite := hcomp ▸ RingHom.finite_algebraMap.2 hBfin
  have hσfin : σ.Finite := RingHom.Finite.of_comp_finite hcfin
  refine ⟨B, inferInstance, inferInstance, hBloc, σ, ⟨hadm, hσinj, hσfin⟩,
    RingHom.IsIntegral.isLocalHom hσfin.to_isIntegral hσinj, ⟨hadm, hσinj.comp hinj, hcfin⟩, ?_⟩
  rw [hcomp]
  exact isGal_integralClosure_of_tower R L

end GlobalTheory.GalClosure
