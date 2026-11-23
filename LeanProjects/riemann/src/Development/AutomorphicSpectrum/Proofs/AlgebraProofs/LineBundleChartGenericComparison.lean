import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleModelDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModelStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkLinePow

section Lists

variable {K : Type*} {σ : Type*}

theorem headAdd_zsmul {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (m : ℤ) (u : K → ℤ)
    (l : List (K → ℤ)) : A ((m • u) :: l) = m * A (u :: l) := by
  let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l
  exact map_zsmul φ m u

theorem map_zsmul_append {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (l r : List (K → ℤ)) : A (l.map (m • ·) ++ r) = m ^ l.length * A (l ++ r) := by
  induction l generalizing r with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.cons_append, headAdd_zsmul hA,
      hp _ _ (List.perm_middle (a := u) (l₁ := l.map (m • ·)) (l₂ := r)).symm, ih,
      hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]
    ring

theorem length_classList (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = n := by
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← h1]
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

theorem polyVal_zsmul {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A) (m : ℤ)
    (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ} (hH : H.IsHomogeneous n) :
    polyVal A (fun s => m • cls s) H = m ^ n * polyVal A cls H := by
  unfold polyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hperm : (classList (fun s => m • cls s) μ).Perm ((classList cls μ).map (m • ·) ++ []) := by
    unfold classList
    rw [List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.coe_toList, Multiset.map_map]
    rfl
  rw [hp _ _ hperm, map_zsmul_append hp hA, length_classList cls hH hμ, List.append_nil]
  ring

end Lists

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isVerticalDivisor_swap {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f where
  degrees := by
    obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  num_not_mem := hD.den_not_mem
  den_not_mem := hD.num_not_mem
  vertical := fun W hW => hD.vertical W fun h => hW (by
    unfold ratDiv at h ⊢
    linarith)
  unit_off_special := by
    intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h

theorem exists_zpow {Ω : Type} [Field Ω] (φ : MRing ι O →+* Ω) {P : Ideal (MRing ι O)} [P.IsPrime]
    {ϖ : O} {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {u : Ω} (hu : u ≠ 0)
    (hfg : φ f * u = φ g) (m : ℤ) :
    ∃ F G : MRing ι O, IsVerticalDivisor P ϖ (m • b) F G ∧ φ F * u ^ m = φ G ∧
      ∀ W, ratDiv P F G W = m * ratDiv P f g W := by
  induction m using Int.induction_on with
  | zero =>
    refine ⟨1, 1, ?_, by simp, fun W => by simp [ratDiv]⟩
    rw [zero_smul]
    exact isVerticalDivisor_one ϖ P
  | succ n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * f, G * g, ?_, ?_, fun W => ?_⟩
    · rw [add_smul, one_smul]
      exact isVerticalDivisor_mul hFG hD
    · rw [zpow_add_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      ring
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.num_not_mem hD.den_not_mem, Pi.add_apply,
        hr]
      ring
  | pred n ih =>
    obtain ⟨F, G, hFG, hv, hr⟩ := ih
    refine ⟨F * g, G * f, ?_, ?_, fun W => ?_⟩
    · rw [sub_smul, one_smul, sub_eq_add_neg]
      exact isVerticalDivisor_mul hFG (isVerticalDivisor_swap hD)
    · rw [zpow_sub_one₀ hu, map_mul, map_mul, ← hv, ← hfg]
      field_simp
    · rw [ratDiv_mul hFG.num_not_mem hFG.den_not_mem hD.den_not_mem hD.num_not_mem, Pi.add_apply,
        hr]
      unfold ratDiv
      ring

theorem pairNum_scale {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {a b : K → ℤ} {f g F G : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (m : ℤ) (hr : ∀ W, ratDiv P F G W = m * ratDiv P f g W)
    {k : ℕ} (hk : 1 ≤ k) {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum P (fun _ : Fin 1 => m • a) (fun _ => 0) (fun _ => F) (fun _ => G)
        (psumExpansion 1 k) Q =
      m ^ k * pairNum P (fun _ : Fin 1 => a) (fun _ => 0) (fun _ => f) (fun _ => g)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hH := isHomogeneous_psumExpansion 1 k i
  have hn : k - 1 + Q.length = d := by omega
  have hcls : (Sum.elim (fun _ : Fin 1 => m • a) (fun _ : Fin 1 => (0 : K → ℤ))) =
      fun s => m • (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => (0 : K → ℤ))) s := by
    funext s
    cases s <;> simp
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  beta_reduce
  rw [hr W]
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  rw [classNum_eq_polyVal _ hH hn, classNum_eq_polyVal _ hH hn, hcls,
    polyVal_zsmul (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW Q) m _ hH]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A T Am : ChartBundle O (mseg x) 1 Ω) (u : Ω) (a : K → ℤ) (m : ℤ), u ≠ 0 → IsLine O x u a A.lat → IsLine O x 1 0 T.lat → SameGeneric O x A T → IsLine O x (u ^ m) (m • a) Am.lat → SameGeneric O x Am T ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 Am T k L Q = m ^ k * ck O x d 1 A T k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM A T Am u a m hu hA hT hS hAm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  have hS' := (BundleExamples.sameGeneric_iff hϖ x A T).mp hS
  obtain ⟨f, g, hD, hfg⟩ := GlobalTheory.T.monomial_ratio_integral_model O Ω K ι x ϖ hϖ d hW' a 0 u⁻¹ (inv_ne_zero hu) (by
    intro s hs
    obtain ⟨h1, h2⟩ := hS' s hs
    constructor
    · obtain ⟨n, hn⟩ := h1 _ ((hA s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hT s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e
    · obtain ⟨n, hn⟩ := h2 _ ((hT s hs _).2 ⟨1, one_mem _, rfl⟩)
      obtain ⟨r, hr, e⟩ := (hA s hs _).1 hn
      refine ⟨n, r, hr, ?_⟩
      rw [smul_eq_mul] at e
      apply mul_left_cancel₀ hu
      field_simp
      linear_combination e)
  have hfg' : aeval x f * u = aeval x g := by
    rw [hfg]
    field_simp
  have : (pointIdeal O x).IsPrime := hW'.multiProj.isPrime
  obtain ⟨F, G, hFG, hv, hr⟩ := exists_zpow
    (aeval x : MRing ι O →ₐ[O] Ω).toRingHom hD hu hfg' m
  have hFG' : IsVerticalDivisor (pointIdeal O x) ϖ (m • a - 0) F G := by
    simpa using hFG
  obtain ⟨hs1, h1⟩ := GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM Am T (u ^ m) 1 (m • a) 0 hAm hT F G hFG'
    (by rw [mul_one]; exact hv)
  obtain ⟨-, h2⟩ := GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM A T u 1 a 0 hA hT f g hD
    (by rw [mul_one]; exact hfg')
  refine ⟨hs1, fun k hk1 hk2 q L Q hQ => ?_⟩
  rw [h1 k hk1 hk2 q L Q hQ, h2 k hk1 hk2 q L Q hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [pairNum_scale hϖ hW' hD m hr hk1
    (by rw [length_classList L hQ hμ]; omega)]
  ring

end GlobalTheory.CompanionTheory.Ar.CkLinePow
