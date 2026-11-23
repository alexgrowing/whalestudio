import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyDivisorDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightPolynomialInDegreesStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.SwapLine

theorem height_comb_horizontal (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (hY : IsArithVar p D) {Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] {e : ℕ}
    (hc : CharZero Γ(Z, ⊤)) (he : topologicalKrullDim Z = (e + 1 : ℕ)) {ι : Type} [Fintype ι] (L : ι → HermLB p) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (e + 1)) := by
  have hZ : IsArithVar (i ≫ p) e := hY.of_isClosedImmersion i hc he
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Z (i ≫ p) e hZ).2 ι (fun j => (L j).restr i)).1
  refine ⟨Ψ, fun n g hg => ?_⟩
  have e₁ : ((comb L n).restr i).Isometric (comb (fun j => (L j).restr i) n) := by
    refine HermLB.icls_eq_iff.1 ?_
    rw [HermLB.icls_pull, icls_comb, icls_comb, map_sum]
    simp only [map_zsmul, ← HermLB.icls_pull]
  exact (e₁.isSelfInter hZ (hg.isSelfInter_restrict hY i rfl)).unique hZ (hΨ.1 n)

def moveExp (n : Fin 5 → ℤ) : Fin 5 → ℤ := ![0, 0, n 2, n 3 + n 0, n 4 + n 1]

theorem aeval_lin_moveExp (n : Fin 5 → ℤ) :
    aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) (lin fun j => (n j : ℝ)) =
      lin fun j => (moveExp n j : ℝ) := by
  simp [lin, Fin.sum_univ_five, moveExp, MvPolynomial.algebraMap_eq]
  ring

theorem sum_moveExp {G : Type*} [AddCommGroup G] (x : Fin 5 → G) (h₀ : x 0 = x 3) (h₁ : x 1 = x 4) (n : Fin 5 → ℤ) :
    ∑ j, n j • x j = ∑ j, moveExp n j • x j := by
  simp [Fin.sum_univ_five, moveExp, add_smul, h₀, h₁]
  try abel

theorem fam5_icls_tens (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B)
    (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (A : HermLB q) :
    (fam5 π w H flB fl A 0).icls + (fam5 π w H flB fl A 1).icls =
      (fam5 π w H flB fl A 3).icls + (fam5 π w H flB fl A 4).icls := by
  have a1 := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
  have a2 := VMetric.isometric_det_pull H π w
  have a3 := (GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).pull π w
  have a4 := HermLB.isometric_pull_tens (VMetric.grLB flB 0 H) (VMetric.grLB flB 1 H) π w
  rw [← HermLB.icls_tens, ← HermLB.icls_tens]
  exact HermLB.icls_eq_iff.2 (a1.trans (a2.trans (a3.symm.trans a4)))

theorem mix_general (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {d : ℕ}
    (hp : IsArithVar p (d + 1)) (L : Fin 5 → HermLB p)
    (hdet : (L 0).icls + (L 1).icls = (L 3).icls + (L 4).icls)
    (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (hΦ : IsArFun L (d + 1) Φ)
    (r : ((L 0).dual.tens (L 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((L 0).dual.tens (L 4)).B r)
    (hiso : ∀ z ∈ (((L 0).dual.tens (L 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((L 0).restr i).Isometric ((L 3).restr i))
    (F : MvPolynomial (Fin 5) ℝ) (hF : aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0)
    (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ) (hFs : F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1)) :
    Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb L n).archInt ((L 0).dual.tens (L 4)) (d + 1) hr := by
  have := hp.isLocallyNoetherian
  have := hp.isNoetherian

  let Aex : Option (Fin 5) → Fin 5 → ℤ := fun o => o.elim (Pi.single 4 1 - Pi.single 0 1) fun j => Pi.single j 1
  have hΦ' := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L Φ hΦ).2.2 (Option (Fin 5))
    (fun o => o.elim ((L 0).dual.tens (L 4)) L) Aex
    (fun o => by
      cases o with
      | none =>
        refine HermLB.icls_eq_iff.1 ?_
        simp [Aex, icls_comb, HermLB.icls_tens, HermLB.icls_dual, Fin.sum_univ_five, Pi.single_apply]
        done
      | some j => exact isometric_comb_single L j)
  let Φ' := Φ ∘ₗ (aeval fun j => lin fun i => (Aex j i : ℝ) :
    MvPolynomial (Option (Fin 5)) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toLinearMap
  have key (P : MvPolynomial (Fin 5) ℝ) : Φ' (X none * rename some P) = Φ ((X 4 - X 0) * P) := by
    have h1 : (lin fun i => (Aex none i : ℝ)) = X 4 - X 0 := by
      simp [Aex, lin, Fin.sum_univ_five, Pi.single_apply]
      ring
    have h2 : (fun j => lin fun i => (Aex (some j) i : ℝ)) = X := by
      funext j
      simp [Aex, lin, Pi.single_apply]
    simp only [Φ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X, aeval_rename]
    rw [h1]
    congr 2
    exact (congrArg (fun f => aeval f P) h2).trans (aeval_X_left_apply P)

  have hex (n : Fin 5 → ℤ) : ∃ g : Y → ℝ, (comb L n).IsArithHeight g := (hC.arExists k Y p (d + 1) hp).1 (comb L n)
  choose ht hht using hex
  have hmix (n : Fin 5 → ℤ) := (hC.arMix k Y p (d + 1) hp (Fin 5) _ L Φ' hΦ' n (ht n) (hht n) r hr).2
  have hfin : (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ)).Finite :=
    (((L 0).dual.tens (L 4)).div hr).finite_support_mult.subset fun z hz => by simpa using hz

  have hloc (z : Y) : ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ∑ n ∈ s, c n * ht n z = 0 := by
    by_cases hz0 : (((L 0).dual.tens (L 4)).div hr).mult z = 0
    · simp [hz0]
    have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hzs : z ∈ (((L 0).dual.tens (L 4)).div hr).supp := CartierDiv.mem_supp_of_mult_ne_zero hz0
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have e03 : ((L 0).restr i).Isometric ((L 3).restr i) := hiso _ hzs Z i rfl
    have e14 : ((L 1).restr i).icls = ((L 4).restr i).icls := by
      have h₁ := congrArg (HermLB.IsomClass.pull i rfl) hdet
      rw [map_add, map_add, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull, ← HermLB.icls_pull,
        HermLB.icls_eq_iff.2 e03] at h₁
      exact add_left_cancel h₁
    have hdim : topologicalKrullDim Z = (d + 1 : ℕ) := GlobalTheory.T.arithmetic_variety_divisor_dimension k Y p (d + 1) hp Z i hz1
    obtain ⟨T, hT⟩ : ∃ T : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ, ∀ (n : Fin 5 → ℤ) (g : Y → ℝ),
        (comb L n).IsArithHeight g → g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ (d + 1)) := by
      rcases hp.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arithmetic_height_polynomial_in_degrees k Y p (d + 1) hp Z i ℓ (d + 1) hdim (Fin 5) L
      · have he' : e + 1 = d + 1 := by
          have := he.symm.trans hdim
          exact_mod_cast this
        obtain ⟨T, hT⟩ := height_comb_horizontal hC hp i hc he L
        exact ⟨T, fun n g hg => (hT n g hg).trans (by rw [he'])⟩
    have hmove (n : Fin 5 → ℤ) : ((comb L n).restr i).Isometric ((comb L (moveExp n)).restr i) := by
      refine HermLB.icls_eq_iff.1 ?_
      rw [HermLB.icls_pull, HermLB.icls_pull, icls_comb, icls_comb, map_sum, map_sum]
      simp only [map_zsmul]
      exact sum_moveExp (fun j => HermLB.IsomClass.pull i rfl (L j).icls) (HermLB.icls_eq_iff.2 e03) e14 n
    have hsum : ∑ n ∈ s, c n * ht n (i (genericPoint Z)) = T (aeval (![X 3, X 4, X 2, X 3, X 4] :
        Fin 5 → MvPolynomial (Fin 5) ℝ) F) := by
      rw [hFs, map_sum, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, map_pow, aeval_lin_moveExp, map_smul, smul_eq_mul,
        GlobalTheory.AdjFlag.height_eq hp (hht n) (hht (moveExp n)) i (hmove n), hT _ _ (hht (moveExp n))]
    rw [hsum, hF, map_zero, mul_zero]

  have e₁ : Φ ((X 4 - X 0) * F) = ∑ n ∈ s, c n * Φ' (X none * rename some (lin fun i => (n i : ℝ)) ^ (d + 1)) := by
    rw [hFs, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_pow, key]
  have e₂ : ∑ n ∈ s, c n * ∑ᶠ z, ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z = 0 := by
    have hf (n : Fin 5 → ℤ) :
        (Function.support fun z => ((((L 0).dual.tens (L 4)).div hr).mult z : ℝ) * ht n z).Finite :=
      hfin.subset (Function.support_mul_subset_left _ _)
    simp_rw [mul_finsum]
    rw [← finsum_sum_comm s _ fun n _ => (hf n).subset (Function.support_mul_subset_right _ _)]
    refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
    rw [← hloc z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e₁]
  simp_rw [hmix, mul_sub]
  rw [Finset.sum_sub_distrib, e₂, zero_sub]

theorem mix_dualTaut_tens_quotBase : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y]
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p)
    (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ), IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ)
      (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) →
      ∀ F : MvPolynomial (Fin 5) ℝ, aeval (![X 3, X 4, X 2, X 3, X 4] : Fin 5 → MvPolynomial (Fin 5) ℝ) F = 0 →
      ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
        Φ ((X 4 - X 0) * F) = -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt
          ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := by
  intro hC k _ B Y _ _ q p d _ hp π w E h H flB fl A Φ hΦ r hr hiso F hF s c hFs
  exact mix_general hC hp (fam5 π w H flB fl A) (fam5_icls_tens k B Y q p π w E h H flB fl A) Φ hΦ r hr hiso F hF s c hFs

end GlobalTheory.CovTest.SwapLine

end
