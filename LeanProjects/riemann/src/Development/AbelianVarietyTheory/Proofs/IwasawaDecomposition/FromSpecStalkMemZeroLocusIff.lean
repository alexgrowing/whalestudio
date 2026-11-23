import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncComponents

theorem fromSpecStalk_mem_zeroLocus_iff {Y : Scheme.{0}} (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (f : Γ(Y, U.1)) (q : PrimeSpectrum (Y.presheaf.stalk x)) :
    Y.fromSpecStalk x q ∈ Y.zeroLocus {f} ↔ Y.presheaf.germ U.1 x hx f ∈ q.asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have e : Y.fromSpecStalk x q =
      hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [Scheme.mem_zeroLocus_iff, e]
  simp only [Set.mem_singleton_iff, forall_eq]
  have h := hU.fromSpec_preimage_basicOpen f
  have h2 : hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) ∈ Y.basicOpen f ↔
      PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ PrimeSpectrum.basicOpen f :=
    iff_of_eq (congrArg (fun V => PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ V) h)
  exact (not_congr h2).trans not_not

theorem effCartier_of_mem_comps {Y : Scheme.{0}} [IsNoetherian Y] {Z : Y.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (C : Closeds Y) (hC : (C : Set Y) ∈ comps (Z.support : Set Y)) :
    FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) := by
  refine effCartier_of_stalkId _ fun x => ?_
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hZ x
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have hO' := hO _ hC
  have hq : ∀ q : PrimeSpectrum (Y.presheaf.stalk x), Y.fromSpecStalk x q ∈ (C : Set Y) ↔
      ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C ∧
        Y.presheaf.germ U.1 x hx (f i) ∈ q.asIdeal := by
    intro q
    have hqO : Y.fromSpecStalk x q ∈ (O : Set Y) := by
      have h : Y.fromSpecStalk x q ∈ Set.range (Y.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at h
      exact Specializes.mem_open h O.isOpen hxO
    have h := Set.ext_iff.1 hO' (Y.fromSpecStalk x q)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
      fromSpecStalk_mem_zeroLocus_iff U x hx] at h
    exact h
  have hCC : C.compl.compl = C := SetLike.coe_injective (compl_compl _)
  by_cases hb : ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C
  · obtain ⟨i, hi, hbi⟩ := hb
    have hp : Prime (Y.presheaf.germ U.1 x hx (f i)) :=
      prime_of_regular_params (fun i => Y.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 i
    haveI : IsDomain (Y.presheaf.stalk x) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
    refine ⟨_, mem_nonZeroDivisors_of_ne_zero hp.ne_zero, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x
      (Y.presheaf.germ U.1 x hx (f i)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨i, hi, hbi, h⟩⟩)
        rintro ⟨j, hj, hbj, h⟩
        by_cases hij : i = j
        · exact hij ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hi hj hij hbi hbj)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  · refine ⟨1, one_mem _, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x 1 fun q => by
      refine not_congr ((hq q).trans ⟨?_, fun h => ?_⟩)
      · rintro ⟨j, hj, hbj, -⟩
        exact absurd ⟨j, hj, hbj⟩ hb
      · exact absurd ((Ideal.eq_top_iff_one _).2 h) q.isPrime.ne_top
    rw [hCC] at h
    rw [h, Ideal.span_singleton_one, Ideal.radical_top]

theorem exists_compList_effCartier (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] [QuasiCompact p] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) :
    ∃ (m : ℕ) (C : Fin m → Closeds Y), FinalTheorems.CompList (B : Set Y) C ∧
      ∀ i, FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal (C i)) := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian Y := {}
  haveI : Finite (comps (B : Set Y)) := (comps_finite _).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (comps (B : Set Y))
  refine ⟨m, fun i => ⟨(e.symm i).1, isClosed_of_mem_comps B.isClosed (e.symm i).2⟩,
    ⟨fun i => (e.symm i).2.1.1, ?_, fun i j hij => ?_⟩, fun i => ?_⟩
  · conv_rhs => rw [← sUnion_comps (B : Set Y), Set.sUnion_eq_iUnion]
    exact e.symm.surjective.iUnion_comp (fun c => (c.1 : Set Y))
  · have hi : Maximal (fun C => IsIrreducible C ∧ C ⊆ (B : Set Y)) (e.symm i).1 := (e.symm i).2
    exact e.symm.injective (Subtype.ext (Set.Subset.antisymm hij (hi.2 (e.symm j).2.1 hij)))
  · refine effCartier_of_mem_comps hB _ ?_
    have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set Y) = B := by simp
    rw [hs]
    exact (e.symm i).2

end GlobalTheory.SncComponents
