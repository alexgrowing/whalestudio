import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreRegular

theorem quot_localization_regular (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (n : Ideal S) [n.IsPrime]
    (hn : n.comap (algebraMap R S) = p) :
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime n))) := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  let N : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P} := ⟨⟨n, inferInstance⟩, PrimeSpectrum.ext hn⟩
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (p.Fiber S),
      q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) = n :=
    ⟨PrimeSpectrum.preimageEquivFiber R S P N,
      congrArg (fun z => z.1.asIdeal) ((PrimeSpectrum.preimageEquivFiber R S P).symm_apply_apply N)⟩
  subst hq
  have hreg : IsRegularRing (p.Fiber S) := GlobalTheory.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have := isRegularRing_iff.mp hreg q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ p q.asIdeal).toRingEquiv

end GlobalTheory.FibreRegular

namespace GlobalTheory.FibreRegular

theorem isRegularLocalRing_stalk_quot_maximalIdeal :
    ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) [Smooth π] (y : Y),
      IsRegularLocalRing (Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  intro X Y π _ y
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ π ⁻¹ᵁ U from hxU) (π ⁻¹ᵁ U).isOpen
  replace hWle : W ≤ π ⁻¹ᵁ U := hWle
  have hs : (π.appLE U W hWle).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) π inferInstance ⟨U, hU⟩ ⟨W, hW⟩ hWle
  letI := (π.appLE U W hWle).hom.toAlgebra
  haveI : Algebra.Smooth Γ(X, U) Γ(Y, W) := hs
  letI := X.presheaf.algebra_section_stalk (⟨π y, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨π y, hxU⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  set p := (hU.primeIdealOf ⟨π y, hxU⟩).asIdeal with hp
  set n := (hW.primeIdealOf ⟨y, hyW⟩).asIdeal with hn

  have e : ∀ r : Γ(X, U), (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) =
      (π.stalkMap y).hom ((X.presheaf.germ U (π y) hxU).hom r) := by
    have e' : π.appLE U W hWle ≫ Y.presheaf.germ W y hyW =
        X.presheaf.germ U (π y) hxU ≫ π.stalkMap y := by
      refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap π U y hxU).symm
      rw [Scheme.Hom.appLE, Category.assoc, Y.presheaf.germ_res]
    intro r
    exact congr($(e').hom r)
  have hmemU : ∀ a : Γ(X, U), (X.presheaf.germ U (π y) hxU).hom a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (π y)) ↔ a ∈ p := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (π y)) p a
  have hmemW : ∀ a : Γ(Y, W), (Y.presheaf.germ W y hyW).hom a ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ↔ a ∈ n := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y) n a
  have hlies : n.comap (algebraMap Γ(X, U) Γ(Y, W)) = p := by
    ext r
    rw [Ideal.mem_comap, ← hmemW, ← hmemU]
    change (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) ∈ _ ↔ _
    rw [e, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
  have hreg := quot_localization_regular Γ(X, U) Γ(Y, W) p n hlies

  have hI : (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom =
      (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (X.presheaf.stalk (π y)), Ideal.map_map,
      Ideal.map_map]
    congr 1
    ext r
    exact (e r).symm
  let eA := IsLocalization.algEquiv n.primeCompl (Y.presheaf.stalk y) (Localization.AtPrime n)
  let eS : Y.presheaf.stalk y ≃+* Localization.AtPrime n := eA.toRingEquiv
  have hcomp : (eS : Y.presheaf.stalk y →+* Localization.AtPrime n).comp
      (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) = algebraMap Γ(Y, W) (Localization.AtPrime n) :=
    RingHom.ext fun r => eA.commutes r
  have hJ : (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Localization.AtPrime n)) =
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom).map
        (eS : Y.presheaf.stalk y →+* Localization.AtPrime n) := by
    rw [hI, Ideal.map_map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)), hcomp]
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv _ _ eS hJ).symm

end GlobalTheory.FibreRegular
