import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionConstantMetricLine

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

theorem mixedDisc_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (hk : A k = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  have h : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ j ∈ S, A j).det = 0 := by
    rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ k),
      Finset.sum_powerset_insert (Finset.notMem_erase k _), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun S hS => ?_
    have hkS : k ∉ S := fun h => Finset.notMem_erase k _ (Finset.mem_powerset.mp hS h)
    have hc : (insert k S).card ≤ D := by simpa using Finset.card_le_univ (insert k S)
    rw [Finset.card_insert_of_notMem hkS] at hc
    rw [Finset.sum_insert hkS, hk, zero_add, Finset.card_insert_of_notMem hkS,
      show D - S.card = D - (S.card + 1) + 1 by omega, pow_succ]
    ring
  rw [h, mul_zero]

theorem maDensity_eq_zero {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (k : Fin D) (c : ℝ)
    (hk : φ k = fun _ => c) (z : Fin D → ℂ) : maDensity φ z = 0 := by
  have h : cxHessian (φ k) z = 0 := by
    rw [hk]
    funext i j
    simp [cxHessian]
  unfold maDensity
  rw [mixedDisc_eq_zero _ k h]
  simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_eq_zero (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (k : Fin e) (c : ℝ) (hk : φ k = fun _ => c) :
    ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hs : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs
      · rw [maDensity_eq_zero _ k c (by rw [hk]), mul_zero]
      · rfl
    simp [hs]
  · rfl

theorem geoNum_last_zero (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ)
    (ha : a (Fin.last n) = 0) : geoNum (n + 1) V a = 0 := by
  rw [geoNum.eq_2]
  simp [ha]

theorem snoc_snoc_swap {α : Type*} {e : ℕ} (L : Fin e → α) (A B : α) :
    (Fin.snoc (Fin.snoc L A : Fin (e + 1) → α) B : Fin (e + 2) → α) =
      (Fin.snoc (Fin.snoc L B : Fin (e + 1) → α) A : Fin (e + 2) → α) ∘
        Equiv.swap (Fin.last (e + 1)) (Fin.last e).castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp
    · have h1 : k.castSucc.castSucc ≠ Fin.last (e + 1) := (Fin.castSucc_lt_last _).ne
      have h2 : k.castSucc.castSucc ≠ (Fin.last e).castSucc := fun h =>
        (Fin.castSucc_lt_last k).ne (Fin.castSucc_injective _ h)
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L A : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa using hA
  · simpa using hL k

theorem points_integral_section_snoc : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) = ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  classical
  intro II hII hDS K _ ι _ P e L A s hP hL hA hs
  obtain ⟨hIS, -, -, -⟩ := hII
  obtain ⟨hperm, -, hrec⟩ := hIS K ι
  set O : HermLine ι := HermLine.ofWeight (K := K) (ι := ι) (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO
  have hOs : IsSmoothHerm O := by
    show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
    exact contDiffOn_const
  have hsnL := smooth_snoc hL hA
  have hsnO := smooth_snoc hL hOs
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have h1 := intersection_constant_metric_line II hIS K ι P (e + 1) (Fin.snoc L A) (-1) hP hsnL
  have h2 := hrec P (e + 1) (Fin.snoc L O) A s a hP hsnO hA ha hsa hsP
  have h3 : II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L A) O) =
      II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L O) A) := by
    rw [snoc_snoc_swap L A O]
    exact hperm P (e + 1 + 1) _ _ hP (smooth_snoc hsnO hA)
  have h4 := h1.symm.trans (h3.trans h2)
  rw [neg_neg, one_mul] at h4
  rw [h4]
  unfold recR
  have hz : arInt P s A (Fin.snoc L O) = 0 :=
    ptsIntegral_eq_zero P _ _ (Fin.last e) 1 (by funext z; simp [hO, HermLine.ofWeight])
  rw [hz, sub_zero]
  refine finsum_congr fun W => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hW : W ∈ divSupp P s
  · have hW' : W ∈ divSupp P s ↔ True := iff_true_intro hW
    by_cases hh : IsHorizontal W
    · have hWa := (hDS K ι P (e + 1) A s W hP ⟨a, ha, hsa, hsP⟩ hW).1 hh
      have hh' : IsHorizontal W ↔ True := iff_true_intro hh
      simp only [hW', hh', and_self, if_true]
      rw [intersection_constant_metric_line II hIS K ι W e L (-1) hWa hL]
      ring
    · have hh' : IsHorizontal W ↔ False := iff_false_intro hh
      simp only [hW', hh', and_false, if_true, if_false]
      rw [geoNum_last_zero e W _ (by simp [hO, HermLine.ofWeight])]
      simp
  · have hW' : W ∈ divSupp P s ↔ False := iff_false_intro hW
    simp only [hW', false_and, if_false]

end RootFieldNumerics
