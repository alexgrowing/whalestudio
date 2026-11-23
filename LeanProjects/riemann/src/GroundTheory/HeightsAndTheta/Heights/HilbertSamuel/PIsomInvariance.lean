import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace IsomInvariance

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_ratSection {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩

theorem snoc_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → HermLine ι) (A B : HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring

theorem update_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) (j : Fin n)
    (B : HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))
  have hL' : ∀ i, IsSmoothHerm (Function.update L j B i) := fun i => by
    by_cases hi : i = j
    · subst hi; simpa using hB
    · simpa [Function.update_of_ne hi] using hL i
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let N : Fin m → HermLine ι := fun i => L (σ i.castSucc)
  have hne : ∀ i : Fin m, σ i.castSucc ≠ j := fun i h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h
  have e1 : L ∘ σ = Fin.snoc N (L j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N]
  have e2 : Function.update L j B ∘ σ = Fin.snoc N B := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N, Function.update_of_ne (hne i)]
  rw [← hI.1 P _ L σ hP hL, ← hI.1 P _ _ σ hP hL', e1, e2]
  exact snoc_eq hR hI N (L j) B hP (fun i => hL _) (hL j) hB hLB

end IsomInvariance

theorem IsomInvariance.proof (hR : Inter.RatR.Statement) : IsomInvariance.Statement := by
  classical
  intro K _ ι _ I hI P n L L' hP hL hL' hiso
  let M : Finset (Fin n) → Fin n → HermLine ι := fun S j => if j ∈ S then L' j else L j
  have hM : ∀ S j, IsSmoothHerm (M S j) := fun S j => by
    by_cases h : j ∈ S
    · simpa [M, h] using hL' j
    · simpa [M, h] using hL j
  have key : ∀ S : Finset (Fin n), I P n L = I P n (M S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [M]
    | insert a S ha ih =>
      have e : M (insert a S) = Function.update (M S) a (L' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [M]
        · simp [M, hj]
      have hMa : M S a = L a := by simp [M, ha]
      rw [ih, e]
      exact IsomInvariance.update_eq hR hI (M S) a (L' a) hP (hM S) (hL' a) (hMa ▸ hiso a)
  have hU : M Finset.univ = L' := by funext j; simp [M]
  rw [key Finset.univ, hU]

end GroundTheory.Heights₂.Heights.HilbertSamuel
