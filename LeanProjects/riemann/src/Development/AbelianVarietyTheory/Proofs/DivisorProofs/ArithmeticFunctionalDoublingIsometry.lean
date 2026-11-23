import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRR

variable {k : Type} [CommRing k] {X B : Scheme.{0}} {p : X ⟶ Sp k} {q : B ⟶ Sp k}

theorem isometric_pull_of_eq (N : HermLB q) {a b : X ⟶ B} (ha : a ≫ q = p) (hb : b ≫ q = p) (e : a = b) :
    (N.pull a ha).Isometric (N.pull b hb) := by
  subst e
  exact HermLB.Isometric.refl _

theorem isometric_pull_pull_self (N : HermLB q) (π : X ⟶ B) (hπ : π ≫ q = p) (f : X ⟶ X) (hf : f ≫ p = p)
    (hfπ : f ≫ π = π) : ((N.pull π hπ).pull f hf).Isometric (N.pull π hπ) := by
  have h : (f ≫ π) ≫ q = p := by rw [hfπ, hπ]
  have R := N.refines_pull_pull π hπ f hf h
  exact (HermLB.isometric_of_chart _ R.le (fun x => R.g X (𝟙 X) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm).trans (isometric_pull_of_eq N h hπ hfπ)

end GlobalTheory.ThetaRR

namespace GlobalTheory.ThetaRR

theorem eq_zero_of_four_pow_mul (g m : ℕ) (x : ℝ) (hm : m ≠ g) (h : (4 : ℝ) ^ g * x = 4 ^ m * x) : x = 0 := by
  have hne : (4 : ℝ) ^ g ≠ 4 ^ m := fun e =>
    hm ((pow_right_injective₀ (by norm_num : (0 : ℝ) < 4) (by norm_num)) e).symm
  have : ((4 : ℝ) ^ g - 4 ^ m) * x = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.ThetaRR

namespace GlobalTheory.ThetaRR

def quartExp : Fin 3 → Fin 3 → ℤ := fun j i => if i = j then ![4, 1, 1] j else 0

theorem lin_quartExp_zero : lin (fun i => ((quartExp 0 i : ℤ) : ℝ)) = MvPolynomial.C 4 * MvPolynomial.X 0 := by
  simp [lin, quartExp, Fin.sum_univ_three]

theorem lin_quartExp_one : lin (fun i => ((quartExp 1 i : ℤ) : ℝ)) = MvPolynomial.X 1 := by
  simp [lin, quartExp, Fin.sum_univ_three]

theorem lin_quartExp_two : lin (fun i => ((quartExp 2 i : ℤ) : ℝ)) = MvPolynomial.X 2 := by
  simp [lin, quartExp, Fin.sum_univ_three]

theorem arFun_vanish_of_quartic : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X B : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : B ⟶ Sp k) (π : X ⟶ B) (hπ : π ≫ q = p) (g : ℕ), IsArithVar p (g + 1) → ∀ (f : X ⟶ X) (hf : f ≫ p = p), f ≫ π = π → f (genericPoint X) = genericPoint X → f.residueDegree (genericPoint X) = 4 ^ g → ∀ (L : HermLB p) (N N' : HermLB q), (L.pull f hf).Isometric (L.pow 4) → ∀ Φ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ, IsArFun ![L, N.pull π hπ, N'.pull π hπ] (g + 1) Φ → Φ (MvPolynomial.X 0 ^ (g + 1) * MvPolynomial.X 2) = 0 ∧ Φ (MvPolynomial.X 0 ^ (g + 2)) = 0 ∧ Φ (MvPolynomial.X 0 ^ (g + 1) * MvPolynomial.X 1) = 0 := by
  intro hC k _ X B _ p q π hπ g hX f hf hfπ hgen hdeg L N N' hL Φ hΦ
  set F : Fin 3 → HermLB p := ![L, N.pull π hπ, N'.pull π hπ] with hF
  set P : Fin 3 → HermLB p := fun i => (F i).pull f hf with hP
  have h4 : f.residueDegree (genericPoint X) ≠ 0 := by rw [hdeg]; positivity
  have h1 : IsArFun P (g + 1) (((4 ^ g : ℕ) : ℝ) • Φ) := by
    have := (hC.arProj k X X p p (g + 1) hX hX f hf hgen h4).2 (Fin 3) F Φ hΦ
    rwa [hdeg] at this
  have hA : ∀ j, (comb F (quartExp j)).Isometric (P j) := by
    intro j
    refine HermLB.icls_eq_iff.1 ?_
    rw [icls_comb, Fin.sum_univ_three]
    fin_cases j
    · simp only [quartExp, hP, hF]
      simp
      rw [HermLB.icls_eq_iff.2 hL, HermLB.icls_pow]
      norm_cast
    · simp only [quartExp, hP, hF]
      simp
      exact HermLB.icls_eq_iff.2 (isometric_pull_pull_self N π hπ f hf hfπ).symm
    · simp only [quartExp, hP, hF]
      simp
      exact HermLB.icls_eq_iff.2 (isometric_pull_pull_self N' π hπ f hf hfπ).symm
  have h2 := ((hC.arIso k X p (g + 1) hX).2 (Fin 3) F Φ hΦ).2.2 (Fin 3) P quartExp hA
  have e := GlobalTheory.ArInt.Model.isArFun_unique hX h1 h2
  have ev : ∀ m : MvPolynomial (Fin 3) ℝ, (4 : ℝ) ^ g * Φ m =
      Φ (MvPolynomial.aeval (fun j => lin fun i => ((quartExp j i : ℤ) : ℝ)) m) := by
    intro m
    have := LinearMap.congr_fun e m
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · refine eq_zero_of_four_pow_mul g (g + 1) _ (by omega) ?_
    rw [ev, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X, lin_quartExp_zero, lin_quartExp_two,
      mul_pow, ← MvPolynomial.C_pow, mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  · refine eq_zero_of_four_pow_mul g (g + 2) _ (by omega) ?_
    rw [ev, map_pow, MvPolynomial.aeval_X, lin_quartExp_zero,
      mul_pow, ← MvPolynomial.C_pow, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  · refine eq_zero_of_four_pow_mul g (g + 1) _ (by omega) ?_
    rw [ev, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X, lin_quartExp_zero, lin_quartExp_one,
      mul_pow, ← MvPolynomial.C_pow, mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]

end GlobalTheory.ThetaRR
