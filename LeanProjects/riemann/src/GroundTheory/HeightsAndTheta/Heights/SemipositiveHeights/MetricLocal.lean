import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExtLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace MetricLocal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem le_of_mem_divSupp {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) : P ≤ W :=
  le_sup_left.trans hW.1.1.2

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mcPts_mono {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem recR_congr_metric (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MRing ι)) {m : ℕ} (L L' : Fin m → HermLine ι) (C C' : HermLine ι) (s : MRing ι)
    (hI : ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = I W m L')
    (ha : ∀ j, (L j).a = (L' j).a) (hh : ∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z)
    (hC : ∀ z ∈ mcPts P, C.h z = C'.h z) :
    recR I P L C s = recR I P L' C' s := by
  classical
  have hdeg : (fun j => (L j).a) = (fun j => (L' j).a) := funext ha
  unfold recR
  congr 1
  · refine finsum_mem_congr rfl fun W hW => ?_
    by_cases hhor : IsHorizontal W
    · rw [if_pos hhor, if_pos hhor, hI W hW hhor]
    · rw [if_neg hhor, if_neg hhor, hdeg]
  · unfold arInt
    refine (ReciprocityTheory.ChartRestriction.G.Geo.ptsLocal K ι P m 0 _ _ _ _ (fun j z hz => ?_) (fun z hz => ?_)).2
    · simp only [hh j z hz]
    · simp only [logNorm, hC z hz]

theorem step {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsRFamily I)
    {P : Ideal (MRing ι)} {m : ℕ} (L L' : Fin m → HermLine ι) (A A' : HermLine ι)
    (hP : IsArithVar P (m + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (ha : ∀ j, (L j).a = (L' j).a) (haA : A.a = A'.a)
    (hh : ∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z) (hhA : ∀ z ∈ mcPts P, A.h z = A'.h z)
    (hlow : ∀ W, IsArithVar W m → P ≤ W → I W m L = I W m L') :
    I P (m + 1) (Fin.snoc L A) = I P (m + 1) (Fin.snoc L' A') := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2
  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := Inter.ThmIUnique.isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := Inter.ThmIUnique.isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := Inter.ThmIUnique.coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := Inter.ThmIUnique.coordMonomial_not_mem hPp c hc e
  have hCa : ∀ D : HermLine ι, D.a = A.a → ∀ k, (D.tensor B).a k = (e k : ℤ) := by
    intro D hD k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    show D.a k + B.a k = _
    rw [hD, hBa]
    exact (Int.toNat_of_nonneg h0).symm

  have diff : ∀ (M : Fin m → HermLine ι) (D : HermLine ι), (∀ j, IsSmoothHerm (M j)) →
      IsSmoothHerm D → D.a = A.a →
      I P (m + 1) (Fin.snoc M D) = recR I P M (D.tensor B) sC - recR I P M B sB := by
    intro M D hM hD hDa
    have h1 := hI.1 P m M D B hP hM hD hB
    rw [hI.2 P m M (D.tensor B) sC e hP hM (isSmoothHerm_tensor hD hB) (hCa D hDa) hsC hsCP,
      hI.2 P m M B sB b hP hM hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = I W m L' := fun X' s hs W hW hhor =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hhor) (le_of_mem_divSupp hW)
  rw [diff L A hL hA rfl, diff L' A' hL' hA' haA.symm]
  congr 1
  · exact recR_congr_metric I P L L' _ _ sC (hor _ sC ⟨e, hCa A rfl, hsC, hsCP⟩) ha hh
      fun z hz => by show A.h z * B.h z = A'.h z * B.h z; rw [hhA z hz]
  · exact recR_congr_metric I P L L' B B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩) ha hh fun _ _ => rfl

end MetricLocal

theorem MetricLocal.full : MetricLocalStatement := by
  intro K _ ι _ I hI
  have hR : IsRFamily I := IsIntersectionFamily.isRFamily hI
  have key : ∀ (n : ℕ) (P : Ideal (MRing ι)) (L L' : Fin n → HermLine ι), IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) →
      (∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z) → I P n L = I P n L' := by
    intro n
    induction n with
    | zero =>
      intro P L L' _ _ _ _ _
      have : L = L' := funext fun j => j.elim0
      rw [this]
    | succ m ih =>
      intro P L L' hP hL hL' ha hh
      rw [← Fin.snoc_init_self L, ← Fin.snoc_init_self L']
      exact MetricLocal.step hR _ _ _ _ hP (fun j => hL j.castSucc) (fun j => hL' j.castSucc)
        (hL _) (hL' _) (fun j => ha j.castSucc) (funext fun k => by rw [ha]) (fun j => hh j.castSucc)
        (hh _) fun W hW hPW => ih W _ _ hW (fun j => hL j.castSucc) (fun j => hL' j.castSucc)
          (fun j => ha j.castSucc) fun j z hz => hh j.castSucc z (MetricLocal.mcPts_mono hPW hz)
  intro P n L L' hP hL hL' ha hh
  exact key n P L L' hP hL hL' ha hh

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
