import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobson
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdicCompletionLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOfResidueFiniteCompleteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfCompletionFlatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedOfResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightOneComapMinimalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedIdealMapMaximalStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.FibreUnram

theorem isReduced_adicCompletion_quotient {A : Type} [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] :
    IsReduced (AdicCompletion (maximalIdeal A) A ⧸ q.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  obtain ⟨e⟩ := GlobalTheory.adicCompletion_quotient_ringEquiv A (maximalIdeal A) q
  haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
  haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra (A ⧸ q)
    haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
  have hj : (maximalIdeal A).map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
    haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
    have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
      rw [map_mul, hb]; exact hu.mul_val_inv
    have h2 : a * b - 1 ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    have h3 : a * b - 1 ∈ maximalIdeal A := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) h2
    have h4 : (1 : A) ∈ maximalIdeal A := by
      have := (maximalIdeal A).sub_mem ((maximalIdeal A).mul_mem_right b ha) h3
      simpa using this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
  haveI := GlobalTheory.CompletionReduced.isReduced_adicCompletion (A ⧸ q) _ hj
  exact isReduced_of_injective e.toRingHom e.injective

theorem map_comap_eq_maximalIdeal
    {A R : Type} [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R] [IsDomain R]
    [IsLocalRing R] (φ : A →+* R) (hR : IsCN R) (hφ : IsEtaleCompletion φ)
    (hu : ((residue R).comp φ).FormallyUnramified) (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1)
    (hq : Q.comap φ ≠ ⊥) :
    (Q.comap φ).map ((algebraMap R (Localization.AtPrime Q)).comp φ) = maximalIdeal (Localization.AtPrime Q) := by
  have L1 := @GlobalTheory.T.exists_adic_completion_lift
  have L2 := @GlobalTheory.T.finite_of_residue_finite_complete
  have L3 := @GlobalTheory.T.flat_of_completion_flat
  have L4 := @GlobalTheory.T.formallyUnramified_of_residue
  have L6a := @GlobalTheory.T.height_one_comap_minimal
  have L6b := @GlobalTheory.T.reduced_ideal_map_maximal
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  obtain ⟨hfl, hm, hfin⟩ := hφ
  obtain ⟨hRn, -, hRc, -⟩ := hR
  haveI := hRn
  haveI := GlobalTheory.CdvrExt.isLocalHom_of_map_maximalIdeal φ hm
  have hinj := GlobalTheory.CdvrExt.injective_of_flat_local φ hfl
  haveI : IsDomain A := hinj.isDomain φ
  have fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal A) A) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  set B := AdicCompletion (maximalIdeal A) A with hB
  set ι := algebraMap A B with hι
  have hmB := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  have hBc : IsAdicComplete (maximalIdeal B) B := by
    rw [hmB]; exact AdicCompletion.isAdicComplete_self _ fg
  have hιfl : ι.Flat := RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _)
  obtain ⟨ψ, hψ⟩ := L1 φ hRc hm
  have hmψ : (maximalIdeal B).map ψ = maximalIdeal R := by
    rw [hmB, Ideal.map_map, hψ, hm]
  have hres : ((residue R).comp ψ).Finite := by
    have : ((residue R).comp ψ).comp ι = (residue R).comp φ := by rw [RingHom.comp_assoc, hψ]
    rw [← this] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hψfin := L2 ψ hBc hRc hmψ hres
  have hψfl := L3 ψ hψfin (by rw [hψ]; exact hfl)
  have hψu := L4 ι ψ hψfin hmψ (by rw [hψ]; exact hu)
  have hqq : Q.comap φ = Q.comap (ψ.comp ι) := by rw [hψ]
  have hmin := L6a ι ψ hιfl hψfl Q hQ (hqq ▸ hq)
  have hJ : (Q.comap φ).map ι ≤ Q.comap ψ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ]
  have hred := isReduced_adicCompletion_quotient (A := A) (Q.comap φ)
  have key := L6b ψ hψfin hψu Q ((Q.comap φ).map ι) hJ hred (fun P hP h1 h2 => hmin P hP (hqq ▸ h1) h2)
  rw [Ideal.map_map, RingHom.comp_assoc, hψ] at key
  exact key

end GlobalTheory.FibreUnram

namespace GlobalTheory.FibreUnram

theorem stalk_map_comap_eq_maximalIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (Scheme.stalkClosedPointTo ξ).hom ≠ ⊥ → (Q.comap (Scheme.stalkClosedPointTo ξ).hom).map ((algebraMap R (Localization.AtPrime Q)).comp (Scheme.stalkClosedPointTo ξ).hom) = maximalIdeal (Localization.AtPrime Q) := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ hR hφ hu Q _ hQ hq
  obtain ⟨-, hess⟩ := GlobalTheory.GModStalk.charZero_essFiniteType_stalk E H D l Xo c Z (ξ (closedPoint R))
  exact map_comap_eq_maximalIdeal  (Scheme.stalkClosedPointTo ξ).hom hR hφ hu Q hQ hq

end GlobalTheory.FibreUnram
