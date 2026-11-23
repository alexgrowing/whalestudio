import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDegree

open MvPolynomial

theorem aeval_mem {A σ : Type} [CommRing A] [Algebra ℚ A] (𝒜 : ℕ → Submodule ℚ A) [SetLike.GradedMonoid 𝒜]
    (w : σ → ℕ) (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 (w i)) {P : MvPolynomial σ ℚ} {j : ℕ}
    (hP : P.IsWeightedHomogeneous w j) : aeval x P ∈ 𝒜 j := by
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial, ← Algebra.smul_def, ← hP (mem_support_iff.1 hd), Finsupp.weight_apply]
  exact Submodule.smul_mem _ _ (SetLike.prod_mem_graded 𝒜 _ _ fun i _ => SetLike.pow_mem_graded _ (hx _))

theorem esymm_hom (r j : ℕ) : (esymm (Fin r) ℚ j).IsHomogeneous j := by
  rw [esymm]
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have := IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin r) ℚ)) (fun _ => 1) fun i _ => isHomogeneous_X _ _
  rwa [Finset.sum_const, smul_eq_mul, Nat.mul_one, (Finset.mem_powersetCard.1 ht).2] at this

theorem comp_aeval_esymm (r j : ℕ) (P : MvPolynomial (Fin r) ℚ) :
    homogeneousComponent j (aeval (fun i : Fin r => esymm (Fin r) ℚ (i + 1)) P) =
      aeval (fun i : Fin r => esymm (Fin r) ℚ (i + 1)) (weightedHomogeneousComponent (fun i : Fin r => (i : ℕ) + 1) j P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial d c =>
    have h1 : (monomial d c : MvPolynomial (Fin r) ℚ).IsWeightedHomogeneous (fun i : Fin r => (i : ℕ) + 1)
        (Finsupp.weight (fun i : Fin r => (i : ℕ) + 1) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    haveI := HomogeneousSubmodule.gradedMonoid (σ := Fin r) (R := ℚ)
    have h2 := aeval_mem (homogeneousSubmodule (Fin r) ℚ) _ (fun i : Fin r => esymm (Fin r) ℚ (i + 1))
      (fun i => esymm_hom r _) h1
    rw [homogeneousComponent_of_mem h2, weightedHomogeneousComponent_of_mem h1]
    split_ifs <;> simp

theorem char_mem {B : BottChern} {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {h : IsRegVar p D}
    (R : ArRing B h) {r : ℕ} (E : HermVB p r) {j : ℕ} (φ : symmetricSubalgebra (Fin r) ℚ)
    (hφ : φ.1.IsHomogeneous j) : R.char E φ ∈ R.gr j := by
  obtain ⟨P, rfl⟩ := (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).surjective φ
  have hv (Q : MvPolynomial (Fin r) ℚ) : (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r) Q).1 =
      aeval (fun i : Fin r => esymm (Fin r) ℚ (i + 1)) Q := esymmAlgHom_apply Q
  have e : weightedHomogeneousComponent (fun i : Fin r => (i : ℕ) + 1) j P = P := by
    apply (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).injective
    apply Subtype.ext
    rw [hv, ← comp_aeval_esymm, ← hv, homogeneousComponent_of_mem hφ, if_pos rfl]
  have e2 : R.char E (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r) P) = aeval (fun i : Fin r => R.cl E (i + 1)) P :=
    congrArg (aeval (fun i : Fin r => R.cl E (i + 1))) ((esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).symm_apply_apply P)
  rw [e2, ← e]
  exact aeval_mem R.gr _ _ (fun i => R.cl_mem E _) (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

theorem char_chPart_tdPart_mem : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (R : ArRing B h) (r : ℕ) (E : HermVB p r) (j : ℕ), R.char E (chPart r j) ∈ R.gr j ∧ R.char E (tdPart r j) ∈ R.gr j := by
  intro B k _ Y p D h R r E j
  refine ⟨char_mem R E _ ?_, char_mem R E _ (homogeneousComponent_isHomogeneous _ _)⟩
  have : (psum (Fin r) ℚ j).IsHomogeneous j :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j
  exact (homogeneousSubmodule (Fin r) ℚ j).smul_mem _ this

end GlobalTheory.CharDegree
