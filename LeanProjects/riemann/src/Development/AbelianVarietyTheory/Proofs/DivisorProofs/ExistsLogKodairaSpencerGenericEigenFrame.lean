import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineCharStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add, map_add]) (fun x y => by
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
