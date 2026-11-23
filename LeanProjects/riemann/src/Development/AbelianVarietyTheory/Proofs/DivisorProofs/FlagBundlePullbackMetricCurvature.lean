import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricLineExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormPowersLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionSwapLineFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleRegularBaseFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleRegularBaseSecondStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockPoint.OddTerm

open HermLB

section Main

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] [IsIntegral Y] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}
  {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules} {h : VMetric q E 2} {H : h.IsCInf} {flB : Vert.Flag E 2}
  {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {A : HermLB q}

theorem geoFun_rel (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1))
    (hreg : ∀ b : B, IsRegularLocalRing (B.presheaf.stalk b))
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    {Ψ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ} (hΨ : IsGeoFun (fam5 π w H flB fl A) (d + 1) Ψ) (K : MvPolynomial (Fin 5) ℝ) :
    Ψ ((X 4 - X 0) * ((X 3 - X 0) * K)) = 0 := by
  have h₁ : ∀ a b : Fin 5, (X a - X b : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    fun a b => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  let A' : HermLB q := A.shift (fun _ => 1) fun _ => rfl
  have hs := comb_shift (L := fam5 π w H flB fl A) (L' := fam5 π w H flB fl A') 2 (pull_shift A 1 π w)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 5) (fam5 π w H flB fl A)).1
  obtain ⟨Φ', hΦ'⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 5) (fam5 π w H flB fl A')).1
  obtain ⟨r, hr, hsupp, -⟩ := GlobalTheory.T.rank_two_flag_rational_sections k B Y q p d hq hp hreg π w E h H flB fl hfl A
  have key : ∀ K' : MvPolynomial (Fin 5) ℝ, K'.IsHomogeneous d →
      Ψ ((X 4 - X 0) * ((X 3 - X 0) * pderiv 2 K')) = 0 := by
    intro K' hK'
    obtain ⟨s, c, hpol⟩ := GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin (d + 1) ((X 3 - X 0) * K')
      (by simpa [add_comm] using (h₁ 3 0).mul hK')
    have e := GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A Φ hΦ r hr hsupp _ (by simp) s c hpol
    have e' := GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A' Φ' hΦ' r hr hsupp _ (by simp) s c hpol
    have e₂ := arFun_shift hC hp 2 hs hΦ hΦ' hΨ ((X 4 - X 0) * ((X 3 - X 0) * K'))
    have e₃ : ∀ n, (comb (fam5 π w H flB fl A') n).archInt
        ((fam5 π w H flB fl A' 0).dual.tens (fam5 π w H flB fl A' 4)) (d + 1) hr = (comb (fam5 π w H flB fl A) n).archInt
        ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr := fun n => by
      simp only [HermLB.archInt, (hs n).chernInt_eq, chernInt_shift]
      rfl
    simp only [e₃] at e'
    rw [e, e', left_eq_add] at e₂
    convert e₂ using 2
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply]
  induction K using MvPolynomial.induction_on' with
  | add K₁ K₂ e₁ e₂ => rw [mul_add, mul_add, map_add, e₁, e₂, add_zero]
  | monomial m a =>
    by_cases hm : m.degree + 1 = d
    · have := key (monomial (m + Finsupp.single 2 1) (a / ((m 2 : ℝ) + 1)))
        (isHomogeneous_monomial _ (by rw [map_add, Finsupp.degree_single, hm]))
      rw [pderiv_monomial] at this
      convert this using 5
      · simp
      · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        field_simp
    · exact hΨ.2 _ (1 + (1 + m.degree)) (by omega) ((h₁ 4 0).mul ((h₁ 3 0).mul (isHomogeneous_monomial _ rfl)))

theorem geoFun_gysin (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1))
    (hreg : ∀ b : B, IsRegularLocalRing (B.presheaf.stalk b))
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    {Ψ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ} (hΨ : IsGeoFun (fam5 π w H flB fl A) (d + 1) Ψ)
    {ΨB : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ} (hB : IsGeoFun ![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] d ΨB)
    (f : MvPolynomial (Fin 3) ℝ) : Ψ (-X 0 * rename (![3, 4, 2] : Fin 3 → Fin 5) f) = ΨB f := by
  have hz := GlobalTheory.ArInt.Model.eq_zero_of_pow d (Ψ ∘ₗ LinearMap.mulLeft ℝ (-X 0) ∘ₗ
    (rename (![3, 4, 2] : Fin 3 → Fin 5) : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap - ΨB) (fun n => by
      set LB3 : Fin 3 → HermLB q := ![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A]
      let T : Fin 2 → Fin 5 → ℤ := ![Pi.single 0 1, fun i => ∑ j, n j * baseExp j i]
      have hT : ∀ j, (comb (fam5 π w H flB fl A) (T j)).Isometric
          ((![VMetric.grLB fl 0 (H.pull π w), (comb LB3 n).pull π w] : Fin 2 → HermLB p) j) := by
        intro j
        fin_cases j
        · exact isometric_comb_single _ 0
        · exact (isometric_comb_comb _ baseExp n).trans ((isometric_comb_congr isometric_baseExp n).trans
            (isometric_comb_pull LB3 n π w))
      have e := GlobalTheory.T.flag_bundle_regular_base_second hC k B Y q p d hq hp hreg π w E h H ⟨flB⟩ fl hfl (comb LB3 n) _ (isGeoFun_subst hΨ _ T hT)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at e ⊢
      rw [hB.1 n, ← e, sub_eq_zero, ← aeval_baseExp, map_pow, aeval_lin]
      simp [T, lin_single])
    (fun P e he hP => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
      rw [hB.2 P e he hP, hΨ.2 _ (1 + e) (by omega) ((isHomogeneous_X _ _).neg.mul hP.rename_isHomogeneous), sub_zero])
  have := LinearMap.congr_fun hz f
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply, sub_eq_zero] using this

theorem arFun_rel (hC : ArCalc) (hq : IsArithVar q d) (hp : IsArithVar p (d + 1))
    (hreg : ∀ b : B, IsRegularLocalRing (B.presheaf.stalk b))
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    {Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun (fam5 π w H flB fl A) (d + 1) Φ)
    {ΨB : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ} (hB : IsGeoFun ![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A] d ΨB)
    (i : ℕ) (R : MvPolynomial (Fin 3) ℝ) (hi : 2 * i ≤ d) (hR : R.IsHomogeneous (d - 2 * i)) :
    Φ ((X 4 - X 0) * ((X 3 - X 0) * ((X 3 + X 4 - 2 * X 0) ^ (2 * i) * rename (![3, 4, 2] : Fin 3 → Fin 5) R))) =
      1 / (2 * (2 * (i : ℝ) + 1)) * ΨB ((X 1 - X 0) ^ (2 * i) * R) := by
  obtain ⟨r, hr, hsupp, hnorm⟩ := GlobalTheory.T.rank_two_flag_rational_sections k B Y q p d hq hp hreg π w E h H flB fl hfl A
  have h₁ : (X 3 - X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  have h₂ : (X 3 + X 4 - 2 * X 0 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := by
    rw [two_mul]
    exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).sub ((isHomogeneous_X _ _).add (isHomogeneous_X _ _))
  obtain ⟨s, c, hpol⟩ := GlobalTheory.IntLinPow.homog_eq_sum_pow_intLin (d + 1) _
    (by convert h₁.mul ((h₂.pow (2 * i)).mul (hR.rename_isHomogeneous (f := (![3, 4, 2] : Fin 3 → Fin 5)))) using 1; omega)
  rw [GlobalTheory.T.arithmetic_function_swap_line_family hC k B Y q p d hq hp π w E h H flB fl A Φ hΦ r hr hsupp _ (by simp) s c hpol]
  exact GlobalTheory.T.flag_bundle_regular_base_first hC k B Y q p d hq hp hreg π w E h H flB fl hfl A ΨB hB r hr hnorm i R hi hR s c hpol

end Main

theorem pow_expand (j : ℕ) : ((X 3 + X 4 - 2 * X 0) ^ (2 * j) : MvPolynomial (Fin 5) ℝ) = (X 4 - X 3) ^ (2 * j) +
    ∑ i ∈ Finset.range j, 4 * ((X 4 - X 0) * ((X 3 - X 0) *
      ((X 3 + X 4 - 2 * X 0) ^ (2 * i) * (X 4 - X 3) ^ (2 * (j - 1 - i))))) := by
  have := (Commute.all ((X 3 + X 4 - 2 * X 0) ^ 2 : MvPolynomial (Fin 5) ℝ) ((X 4 - X 3) ^ 2)).geom_sum₂_mul j
  rw [pow_mul, pow_mul, ← sub_eq_iff_eq_add', ← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_mul, pow_mul]
  ring

theorem arFun_pow_eq_oddHarm_mul : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf), Nonempty (Vert.Flag E 2) →
    ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ (j : ℕ) (P : MvPolynomial (Fin 2) ℝ), 1 ≤ j → 2 * j ≤ d + 2 → P.IsHomogeneous (d + 2 - 2 * j) →
        Φ ((X 1 - X 0) ^ (2 * j) * aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P) =
          oddHarm j * Ψ ((X 1 - X 0) ^ (2 * j - 1) * aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P) := by
  intro hC k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ j P hj hjd hP
  obtain ⟨flB⟩ := hflB
  obtain ⟨⟨Φ5, hΦ5⟩, Ψ5, hΨ5⟩ := (hC.arExists k Y p (d + 1) hp).2 (Fin 5) (fam5 π w H flB fl A)
  obtain ⟨ΨB, hB⟩ := ((hC.arExists k B q d hq).2 (Fin 3) ![VMetric.grLB flB 0 H, VMetric.grLB flB 1 H, A]).2
  have eΦ := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ
    (((hC.arIso k Y p (d + 1) hp).2 (Fin 5) _ Φ5 hΦ5).2.2 (Fin 3) _ lineExp isometric_lineExp)
  have eΨ := GlobalTheory.ArInt.Model.isGeoFun_unique hΨ (isGeoFun_subst hΨ5 _ lineExp isometric_lineExp)
  rw [lin_lineExp] at eΦ eΨ
  set M : MvPolynomial (Fin 3) ℝ := aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P with hM
  have hMh : M.IsHomogeneous (d + 2 - 2 * j) := by
    have := hP.aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) (n := 1) fun i => by
      fin_cases i
      · exact (isHomogeneous_X _ _).add (isHomogeneous_X _ _)
      · exact isHomogeneous_X _ _
    rwa [one_mul] at this
  have eM : aeval (![X 0, X 3 + X 4 - X 0, X 2] : Fin 3 → MvPolynomial (Fin 5) ℝ) M =
      rename (![3, 4, 2] : Fin 3 → Fin 5) M := by
    rw [hM, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext i : 1
    fin_cases i <;> simp
  have eu : aeval (![X 0, X 3 + X 4 - X 0, X 2] : Fin 3 → MvPolynomial (Fin 5) ℝ) (X 1 - X 0 : MvPolynomial (Fin 3) ℝ) =
      X 3 + X 4 - 2 * X 0 := by
    simp
    ring
  have er : ∀ (m : ℕ) (f : MvPolynomial (Fin 3) ℝ), (X 4 - X 3) ^ m * rename (![3, 4, 2] : Fin 3 → Fin 5) f =
      rename (![3, 4, 2] : Fin 3 → Fin 5) ((X 1 - X 0) ^ m * f) := fun m f => by simp
  have h₁ : (X 1 - X 0 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  have four : ∀ f : MvPolynomial (Fin 5) ℝ, 4 * f = (4 : ℝ) • f := fun f => by rw [smul_eq_C_mul]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
  rw [eΦ, eΨ]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, eM, eu]

  have eL : Φ5 ((X 3 + X 4 - 2 * X 0) ^ (2 * (l + 1)) * rename (![3, 4, 2] : Fin 3 → Fin 5) M) =
      oddHarm (l + 1) * (2 * ΨB ((X 1 - X 0) ^ (2 * l) * M)) := by
    rw [pow_expand, add_mul, map_add, er, arFun_base hC hq hp hΦ5, zero_add, Finset.sum_mul, map_sum, oddHarm,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have := arFun_rel hC hq hp hreg hfl hΦ5 hB i ((X 1 - X 0) ^ (2 * (l - i)) * M) (by omega)
      (by convert (h₁.pow (2 * (l - i))).mul hMh using 1; omega)
    rw [← er, ← mul_assoc ((X 1 - X 0) ^ _), ← pow_add, show 2 * i + 2 * (l - i) = 2 * l by omega] at this
    rw [Nat.add_sub_cancel, mul_assoc, four, map_smul]
    simp only [mul_assoc] at this ⊢
    rw [this, smul_eq_mul]
    field_simp
    ring

  have eR : Ψ5 ((X 3 + X 4 - 2 * X 0) ^ (2 * (l + 1) - 1) * rename (![3, 4, 2] : Fin 3 → Fin 5) M) =
      2 * ΨB ((X 1 - X 0) ^ (2 * l) * M) := by
    have e₁ := geoFun_gysin hC hq hp hreg hfl hΨ5 hB ((X 1 - X 0) ^ (2 * l) * M)
    have e₂ := geoFun_base hC hq hp hΨ5 ((X 0 + X 1) * ((X 1 - X 0) ^ (2 * l) * M))
    have e₃ := geoFun_rel hC hq hp hreg hfl hΨ5 (∑ i ∈ Finset.range l, 4 * ((X 3 + X 4 - 2 * X 0) ^ (2 * i) *
      (X 4 - X 3) ^ (2 * (l - 1 - i))) * ((X 3 + X 4 - 2 * X 0) * rename (![3, 4, 2] : Fin 3 → Fin 5) M))
    have e₄ : ((X 3 + X 4 - 2 * X 0) ^ (2 * (l + 1) - 1) * rename (![3, 4, 2] : Fin 3 → Fin 5) M :
        MvPolynomial (Fin 5) ℝ) = -X 0 * rename (![3, 4, 2] : Fin 3 → Fin 5) ((X 1 - X 0) ^ (2 * l) * M) +
        -X 0 * rename (![3, 4, 2] : Fin 3 → Fin 5) ((X 1 - X 0) ^ (2 * l) * M) +
        rename (![3, 4, 2] : Fin 3 → Fin 5) ((X 0 + X 1) * ((X 1 - X 0) ^ (2 * l) * M)) +
        (X 4 - X 0) * ((X 3 - X 0) * ∑ i ∈ Finset.range l, 4 * ((X 3 + X 4 - 2 * X 0) ^ (2 * i) *
          (X 4 - X 3) ^ (2 * (l - 1 - i))) * ((X 3 + X 4 - 2 * X 0) * rename (![3, 4, 2] : Fin 3 → Fin 5) M)) := by
      rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega, pow_succ, pow_expand, add_mul, add_mul, Finset.sum_mul,
        Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · simp
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        ring
    rw [e₄, map_add, map_add, map_add, e₁, e₂, e₃]
    ring
  rw [eL, eR]

end GlobalTheory.BlockPoint.OddTerm

end
