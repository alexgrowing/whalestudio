import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
