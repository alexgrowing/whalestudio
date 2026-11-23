import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantDerivativeNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqHilbertDegreeOfIsChowForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionFiniteInOpenOffBadFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowFormStatement

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BertiniTop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem bertini : Quoted → Bertini := by
  intro hq F _ _ T hG hB δ f hf
  obtain ⟨-, hdeg, hdim⟩ :=
    GlobalTheory.ImageDegree.degree_image_eq_topSelf hq F T.toLinSys hG.alg.variety hG.alg.bpf hB
  have hprime : T.imageIdeal.IsPrime := HeightExists.isPrime_imageIdeal (S := T.toLinSys) hG.alg.variety
  have hhom : ∀ a ∈ T.imageIdeal, ∀ n : ℕ, homogeneousComponent n a ∈ T.imageIdeal := by
    intro a ha n
    have h := T.toLinSys.isHomogeneous_imageIdeal n ha
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin T.N) F) a n : MvPolynomial (Fin T.N) F) =
      homogeneousComponent n a from MvPolynomial.decomposition.decompose'_apply a n] at h
  have hδ : (δ : ℤ) = T.del := by
    rw [GlobalTheory.ChowDegree.degree_eq_hilbertDegree_of_isChowForm F T.D T.N δ T.imageIdeal f hf hprime hhom]
    exact hdeg
  refine ⟨hδ, ?_⟩
  obtain ⟨d₁, g₁, hg₁, hg₁I, hg₁v⟩ := GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary F T hG hB
  obtain ⟨d₂, g₂, hg₂, hg₂I, hg₂f⟩ := GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨Q₁, hQ₁, hQ₁v⟩ := GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone F T.D T.N (d₁ + d₂) T.imageIdeal (g₁ * g₂) hG.alg.variety.one_le hprime hhom
    hdim (hg₁.mul hg₂) fun h => (hprime.mem_or_mem h).elim hg₁I hg₂I
  obtain ⟨Q₂, hQ₂, -, hQ₂n⟩ :=
    GlobalTheory.PencilDisc.exists_poly_noSquare F T.D T.N δ f hf.isChowFormInt.pos hf.homog hf.irred
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun E _ _ s hs => ?_⟩
  have hs' : aeval (fun p : Fin T.D × Fin T.N => algebraMap E (AlgebraicClosure E) (s p.1 p.2)) (Q₁ * Q₂) ≠ 0 := by
    have h := MvPolynomial.aeval_algebraMap_apply (AlgebraicClosure E)
      (fun p : Fin T.D × Fin T.N => s p.1 p.2) (Q₁ * Q₂)
    exact fun h0 => hs ((map_eq_zero (algebraMap E (AlgebraicClosure E))).1 (h.symm.trans h0))
  rw [map_mul] at hs'
  have hns : NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) :=
    hQ₂n _ _ (right_ne_zero_of_mul hs')
  obtain ⟨hfin, hopen⟩ := GlobalTheory.T.linearSection_finite_inOpen_off_badForm F T hG δ f hf (g₁ * g₂)
    (fun K _ _ x hx => by rw [map_mul, hg₁v K x hx, zero_mul])
    (fun K _ _ y => (hg₂f K y).subset fun x hx => ⟨right_ne_zero_of_mul (by simpa only [map_mul] using hx.1), hx.2⟩)
    E s hns.1 fun x hx h0 => by
      refine left_ne_zero_of_mul hs' (hQ₁v (AlgebraicClosure E) (fun i j => algebraMap E _ (s i j)) _
        (hG.alg.bpf.coords_ne_zero _) (fun a ha => ?_) h0 ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx))
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 ha
      rwa [LinSys.baseHom_ptOver] at this
  exact GlobalTheory.T.linearSection_etale_of_squarefree_chowForm F T hG δ f hf hδ E s hfin hopen hns

end GlobalTheory.BertiniTop
