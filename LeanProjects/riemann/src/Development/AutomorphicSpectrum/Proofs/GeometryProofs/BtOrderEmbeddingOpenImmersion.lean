import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbeddingBaseChangeCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCoverStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExistsStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btEmb_localData (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (R' : Type) [CommRing R'] [IsDomain R'] [HenselianLocalRing R'] [Algebra R R']
    [IsIntegrallyClosed R'] (hflat : Module.Flat R R') :
    ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of (Γ'.btOrder ⊤)))
      (ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤) (U : Γ'.G.left.Opens),
      (∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) ∧
      IsOpenImmersion (U.ι ≫ j') ∧ Γ'.TranslatesCover (Γ'.btOrder ⊤) j' U ∧
      ∀ x : Γ'.G.left, Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) (j' x) =
        IsLocalRing.closedPoint R' → x ∈ U := by
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  have hinj : Function.Injective (algebraMap R R') := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular R' r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R') (mem_nonZeroDivisors_of_ne_zero hr0)
    have : r • (1 : R') = r • (0 : R') := by
      simp [Algebra.smul_def, hr]
    exact one_ne_zero (hreg this)
  obtain ⟨Γ', F, hbc⟩ := GlobalTheory.T.exists_base_change_group R T Γ R' (algebraMap R R') hinj
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := GlobalTheory.T.henselian_quasi_finite_finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := GlobalTheory.T.isFinOpenSub_of_finite R' T Γ' U hUfin hUcl
  obtain ⟨j', hj'⟩ := (GlobalTheory.T.existsUnique_btOrder_embedding R' T Γ').exists
  have hbt := GlobalTheory.T.btOrder_flat_base_change R T Γ R' Γ' F hbc hflat
  have hfull : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
    obtain ⟨d, hd, hf⟩ := hA.full
    exact ⟨d, fun h => hd (hinj (by simpa using h)), hf⟩
  have hext := (GlobalTheory.T.hopf_order_scalar_extension R T R' (Γ.btOrder ⊤) hA hfull).2
  have hext' : ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
      ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
    rw [hbt]; exact hext
  obtain ⟨e, he⟩ := hext'
  let iL : R' →+* R' ⊗[R] (Γ.btOrder ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let iR : (Γ.btOrder ⊤) →+* R' ⊗[R] (Γ.btOrder ⊤) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom
  let ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤ := (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤).comp iR
  have hψ : ∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t) := fun a t => he a t
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (Γ.btOrder ⊤))
  let eH : CommRingCat.of (R' ⊗[R] (Γ.btOrder ⊤)) ⟶ CommRingCat.of (Γ'.btOrder ⊤) :=
    CommRingCat.ofHom (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤)
  haveI : IsIso eH := (e.toRingEquiv.toCommRingCatIso).isIso_hom
  have hb : Spec.map (CommRingCat.ofHom ψ) = Spec.map eH ≫ Spec.map (CommRingCat.ofHom iR) := by
    rw [← Spec.map_comp]; rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) =
      Spec.map eH ≫ Spec.map (CommRingCat.ofHom iL) := by
    rw [← Spec.map_comp]
    congr 2
    ext r t
    exact congrArg (fun y : Γ'.btOrder ⊤ => y.1 t) (e.commutes r).symm
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    refine IsPullback.of_iso sq.flip (asIso (Spec.map eH)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hb]
    · simp [hq]
    · simp
    · simp
  have hw : F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
    GlobalTheory.T.embedding_base_change_compat R T Γ R' Γ' F hbc _ _ ψ hψ j j' hj hj'
  have hsq2 : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hw hsq
    rw [hj'.isOver, hj.isOver]
    exact hbc.cart
  obtain ⟨ho, hTC⟩ := GlobalTheory.T.btOrder_embedding_open_cover R' T Γ' U hU j' hj'
  refine ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, ho, hTC, fun x hx => hUcl x ?_⟩
  rw [← hj'.isOver]
  simpa using hx

theorem btEmb_specMap_asIdeal {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom φ) x).asIdeal = Ideal.comap φ x.asIdeal := rfl

theorem isOpenImmersion_emb_and_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  intro R _ _ _ _ T _ _ Γ j hj
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  refine ⟨?_, ?_⟩
  · haveI := hA.finite
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [hj.isOver]; exact Γ.finPres
    haveI := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
    refine GlobalTheory.T.flat_local_extension_exists R Γ.G.left _ j (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) ?_
    intro P _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R P
    obtain ⟨Γ', F, j', ψ, U, -, hsq, hsq2, ho, -, hcl⟩ := btEmb_localData R T Γ j hj R' hflat
    exact ⟨R', inferInstance, inferInstance, inferInstance, Γ'.G.left, _, j', _, F, _, U, hflat, hcomap, hsq, hsq2, ho, hcl⟩
  · intro P
    let p : Ideal R := P.asIdeal.comap (algebraMap R (Γ.btOrder ⊤))
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R p
    obtain ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, -, hTC, -⟩ := btEmb_localData R T Γ j hj R' hflat
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R R'))) P (IsLocalRing.closedPoint R')
      (PrimeSpectrum.ext hcomap.symm)
    let Q := hsq.isoPullback.inv z
    have hQ : Spec.map (CommRingCat.ofHom ψ) Q = P := by
      rw [← hz1]
      change (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ)) z = _
      rw [hsq.isoPullback_inv_fst]
    obtain ⟨t, g', -, H⟩ := hTC Q
    refine ⟨t, F g', trivial, fun f f' hff => ?_⟩
    have h1 := H (ψ f) (ψ f') (fun h => by rw [hψ, hψ, hff])
    have hg : (j (F g')).asIdeal = Ideal.comap ψ (j' g').asIdeal := by
      rw [← btEmb_specMap_asIdeal]
      change ((F ≫ j) g').asIdeal = ((j' ≫ Spec.map (CommRingCat.ofHom ψ)) g').asIdeal
      rw [hsq2.w]
    rw [hg, ← hQ, btEmb_specMap_asIdeal]
    exact h1

end GlobalTheory.CompanionTheory.Ar.BT
