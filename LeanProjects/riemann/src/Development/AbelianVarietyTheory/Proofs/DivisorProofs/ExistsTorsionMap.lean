import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RaynaudTorsionMap

open GlobalTheory.KernelNoTorsion GlobalTheory.TangentPow GlobalTheory.TorsionCharacter GlobalTheory.HTLat.OmegaRank

theorem ptMap_inj {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    {φ ψ : A →ₐ[O] R} (h : ptMap φ = ptMap ψ) : φ = ψ := by
  have e := Spec.map_injective (congrArg CommaMorphism.left h)
  exact AlgHom.ext fun z => congrArg (fun k => k.hom z) e

theorem exists_lim_affine {p : ℕ} {O A B : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B]
    [Algebra O B] (hc : IsAdicComplete (Ideal.span {(p : B)}) B)
    (y : ∀ m : ℕ, specO O (B ⧸ Ideal.span {(p : B) ^ m}) ⟶ specO O A)
    (hy : ∀ m : ℕ, ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow (p : B) (Nat.le_succ m)))) ≫ y (m + 1) = y m) :
    ∃ Q : specO O B ⟶ specO O A, ∀ m, ptMap (redR p O B m) ≫ Q = y m := by
  choose a ha using fun m => exists_ptMap (y m)
  obtain ⟨L, hL⟩ := ChPt.algLimSt O A B (p : B) hc a (by
    intro m z w hw
    have e := hy m
    rw [ha, ha, ptMap_comp_ptMap] at e
    have e' := congrArg (fun k => k z) (ptMap_inj e)
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : B) (Nat.le_succ m)))) hw).trans e')
  exact ⟨ptMap L, fun m => by rw [ptMap_comp_ptMap, ha, ← hL m]⟩

theorem exists_torsion_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [StarRing Λ] (P P' : Point p v O Λ) (gm : P.G ⟶ P'.G), IsMonHom gm → ∀ N : ℕ, 1 ≤ N → ∃ dl : Semi.torsion P.Gt N ⟶ Semi.torsion P'.Gt N, ∀ (R : Type) [CommRing R] [Algebra O R] (hR : IsNilpotent (p : R)) (w : specO O R ⟶ Semi.torsion P.Gt N), P'.cmp R hR (w ≫ dl ≫ Semi.torsion.ι P'.Gt N) = P.cmp R hR (w ≫ Semi.torsion.ι P.Gt N) ≫ gm := by
  intro p _ C _ v O _ _ _ hO Λ _ _ P P' gm hgm N hN
  haveI := P.isLocalRing
  haveI := (P.finite_flat N hN).1
  haveI := (P.finite_flat N hN).2
  haveI := (P'.finite_flat N hN).1
  haveI := (P'.finite_flat N hN).2
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_free (torsion P.Gt N)
  obtain ⟨A, _, _, _, _, ⟨e'⟩⟩ := exists_finite_free (torsion P'.Gt N)
  have hc : IsAdicComplete (Ideal.span {(p : B)}) B := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hO B
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  let y : ∀ m : ℕ, specO O (B ⧸ Ideal.span {(p : B) ^ m}) ⟶ P'.Gt := fun m =>
    (P'.cmp _ (nilpR m)).symm
      (P.cmp _ (nilpR m) (ptMap (redR p O B m) ≫ e.hom ≫ torsion.ι P.Gt N) ≫ gm)
  have hyN : ∀ m, y m ^ N = 1 := fun m => by
    simp only [y]
    rw [← map_pow, ← MonObj.pow_comp, ← map_pow, ← MonObj.comp_pow, ← MonObj.comp_pow,
      torsionι_pow, MonObj.comp_one, MonObj.comp_one, map_one, MonObj.one_comp, map_one]
  obtain ⟨Q, hQ⟩ := exists_lim_affine hc (fun m => torsionLift (y m) (hyN m) ≫ e'.inv) fun m => by
    rw [← Category.assoc]
    congr 1
    apply torsion_hom_ext
    rw [Category.assoc, torsionLift_ι, torsionLift_ι]
    apply (P'.cmp _ (nilpR m)).injective
    simp only [y]
    rw [P'.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, ← Category.assoc, ← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m),
      ← Category.assoc (ptMap _) (ptMap _), factor_redR]
  refine ⟨e.inv ≫ Q ≫ e'.hom, fun R _ _ hR w => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ e.inv)
  obtain ⟨m, hm⟩ := id hR
  let φ : (B ⧸ Ideal.span {(p : B) ^ m}) →ₐ[O] R := Ideal.Quotient.liftₐ _ ψ fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_pow, map_natCast, hm, zero_mul]
  have hw : w = ptMap φ ≫ ptMap (redR p O B m) ≫ e.hom := by
    rw [← Category.assoc, ptMap_comp_ptMap, show φ.comp (redR p O B m) = ψ from rfl, ← hψ,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : w ≫ (e.inv ≫ Q ≫ e'.hom) ≫ torsion.ι P'.Gt N = ptMap φ ≫ y m := by
    rw [hw]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (ptMap (redR p O B m)), hQ, Category.assoc, Iso.inv_hom_id_assoc,
      torsionLift_ι]
  rw [h1, P'.cmp_nat _ _ (nilpR m) hR, MulEquiv.apply_symm_apply, ← Category.assoc,
    ← P.cmp_nat _ _ (nilpR m) hR, hw]
  simp only [Category.assoc]

end GlobalTheory.RaynaudTorsionMap
