import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreClosureNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GenericProjClosureDivisor

noncomputable section

theorem SegreFlagClosureCut.proof (hC3 : CutByEffectiveDivisor.Statement.{0})
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hSec : SegreFlagCutSection.Statement) (hCon : SegreFlagCutContraction.Statement) :
    SegreFlagClosureCut.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht k hk f₁ g₁ f₂ g₂ hv₁ hg₁ h₂ n z z' fz gz hz m A hA As Bs hAs hBs Q hQ
  classical
  set pt1 := flagClosurePt y w e φ φ' t (k + 1) with hpt1
  set pt0 := flagClosurePt y w e φ φ' t k with hpt0
  set cls := closureDeg (zetaFirst a₀) (Fin.append x z) with hcls
  set cls' := closureDeg (zetaSecond a₀') (Fin.append x' z') with hcls'
  set Q' := Q.map liftPairDeg with hQ'
  have hQlen : Q'.length = Q.length := List.length_map _
  set FV : Fin (N + n) → MRing ι O := Fin.append f fz with hFV
  set GV : Fin (N + n) → MRing ι O := Fin.append g gz with hGV
  have hvV : ∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x z j - Fin.append x' z' j) (FV j) (GV j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [hFV, hGV, Fin.append_left] using hF.vertical i
    · simpa only [hFV, hGV, Fin.append_right] using hz i
  have hpt : ∀ (l : ℕ) (p : Σ k, ι k),
      flagClosurePt y w e φ φ' t l ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p) := fun _ _ => rfl

  have hliftV : ∀ (l : ℕ) (j : Fin (N + n)), IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t l)) ϖ
      (cls (Fin.natAdd 1 j) - cls' (Fin.natAdd 1 j)) (liftPairForm M M' (FV j)) (liftPairForm M M' (GV j)) := by
    intro l j
    have h := (hvV j).liftPair (M := M) (M' := M') (hpt l)
    rwa [liftPairDeg_sub, ← closureDeg_natAdd (zetaFirst a₀), ← closureDeg_natAdd (zetaSecond a₀')] at h

  have hModk := hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht
  have hM1 : IsModelOver (pointIdeal O pt1) (d + k) := by
    have h := (hModk (k + 1) (by omega) (by omega)).1
    rwa [show d + (k + 1 - 1) = d + k by omega] at h
  haveI : (pointIdeal O pt1).IsPrime := hM1.multiProj.isPrime

  have havoid : ∀ j, Fin.append FV GV j ∉ pointIdeal O y := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact (hvV i).num_not_mem
    · rw [Fin.append_right]
      exact (hvV i).den_not_mem
  obtain ⟨cs, ch, s, h, f₃, g₃, hs, hh, hdeg, hsP, hhP, hsv, hdiv, hv₃, hg₃, h₃0, hgen⟩ :=
    hSec O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
      ((N + n) + (N + n)) (Fin.append FV GV) havoid
  rw [← hpt1] at hsP hhP hsv hv₃ hg₃ hdiv hgen
  rw [← hpt0] at hdiv h₃0
  set F3 := closureForm M M' f₃ FV with hF3
  set G3 := closureForm M M' g₃ GV with hG3
  set ζi : Fin (1 + (N + n)) := Fin.castAdd (N + n) (0 : Fin 1) with hζi
  set ki : Fin (N + n) := Fin.castAdd n ⟨k, hk⟩ with hki
  set xi : Fin (1 + (N + n)) := Fin.natAdd 1 ki with hxi
  have hv3 : ∀ i, IsVerticalDivisor (pointIdeal O pt1) ϖ (cls i - cls' i) (F3 i) (G3 i) := by
    intro i
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · obtain rfl : i0 = 0 := Subsingleton.elim _ _
      rw [hF3, hG3, closureForm_zero, closureForm_zero, hcls, hcls', closureDeg_zero, closureDeg_zero]
      exact hv₃
    · rw [hF3, hG3, closureForm_natAdd, closureForm_natAdd]
      exact hliftV (k + 1) j

  have h13 : ratDiv (pointIdeal O pt1) f₁ g₁ = ratDiv (pointIdeal O pt1) f₃ g₃ := by
    obtain ⟨b1, b1', hb1, hb1', hb1d⟩ := hv₁.degrees
    obtain ⟨b3, b3', hb3, hb3', hb3d⟩ := hv₃.degrees
    refine ratDiv_eq_of_sub_mem hv₁.num_not_mem hv₁.den_not_mem hv₃.num_not_mem hv₃.den_not_mem
      (cross_mem hb1 hb1' hb3 hb3' (fun o => ?_) hg₁ hg₃)
    rw [congrFun hb1d o, congrFun hb3d o]
  have hLHS : pairNum (pointIdeal O pt1) cls cls' (closureForm M M' f₁ FV) (closureForm M M' g₁ GV) As Q' =
      pairNum (pointIdeal O pt1) cls cls' F3 G3 As Q' := by
    refine pairNum_congr_ratDiv (fun i => ?_) As Q'
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · obtain rfl : i0 = 0 := Subsingleton.elim _ _
      rw [hF3, hG3, closureForm_zero, closureForm_zero, closureForm_zero, closureForm_zero]
      exact h13
    · rw [hF3, hG3, closureForm_natAdd, closureForm_natAdd, closureForm_natAdd, closureForm_natAdd]
  rw [hLHS]

  obtain ⟨Bs₀, hBs₀, hBs₀m⟩ : ∃ Bs₀ : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ,
      IsPairExpansion m A Bs₀ ∧ (m = 0 → Bs₀ = 0) := by
    by_cases hm : m = 0
    · subst hm
      refine ⟨0, ⟨?_, fun _ => isHomogeneous_zero _ _ _⟩, fun _ => rfl⟩
      rw [eq_C_of_isHomogeneous_zero hA]
      simp
    · exact ⟨Bs, hBs, fun h0 => absurd h0 hm⟩

  set y' : MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ := X (Sum.inr ζi) + X (Sum.inr xi) with hy'
  set E1 : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ :=
    Pi.single ζi (rename Sum.inl A) + Pi.single xi (rename Sum.inl A) with hE1
  set E2 : Fin (1 + (N + n)) → MvPolynomial (Fin (1 + (N + n)) ⊕ Fin (1 + (N + n))) ℤ :=
    fun i => y' * Bs₀ i with hE2
  have hyA : ((X ζi + X xi) * A : MvPolynomial (Fin (1 + (N + n))) ℤ).IsHomogeneous (m + 1) := by
    have h := ((isHomogeneous_X ℤ ζi).add (isHomogeneous_X ℤ xi)).mul hA
    rwa [add_comm 1 m] at h
  have hCs : IsPairExpansion (m + 1) ((X ζi + X xi) * A) (E1 + E2) := by
    refine ⟨?_, fun i => ?_⟩
    · have e1 : ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * (E1 + E2) i =
          (X (Sum.inl ζi) - X (Sum.inr ζi)) * rename Sum.inl A + (X (Sum.inl xi) - X (Sum.inr xi)) * rename Sum.inl A +
            y' * ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Bs₀ i := by
        simp only [hE1, hE2, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e1, ← hBs₀.expansion]
      simp only [hy', map_mul, map_add, rename_X]
      ring
    · simp only [Pi.add_apply, hE1, hE2, Nat.add_sub_cancel]
      refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
      · rw [Pi.single_apply]
        split_ifs
        · exact hA.rename_isHomogeneous
        · exact isHomogeneous_zero _ _ _
      · rw [Pi.single_apply]
        split_ifs
        · exact hA.rename_isHomogeneous
        · exact isHomogeneous_zero _ _ _
      · by_cases hm : m = 0
        · rw [hBs₀m hm, Pi.zero_apply, mul_zero]
          exact isHomogeneous_zero _ _ _
        · have h := ((isHomogeneous_X ℤ (Sum.inr ζi : Fin (1 + (N + n)) ⊕ Fin (1 + (N + n)))).add
            (isHomogeneous_X ℤ (Sum.inr xi))).mul (hBs₀.homogeneous i)
          rwa [show 1 + (m - 1) = m by omega] at h
  have hExp1 := hExp O ϖ hϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M') (pointIdeal O pt1) (d + k) hM1
    (1 + (N + n)) cls cls' F3 G3 hv3 (m + 1) ((X ζi + X xi) * A) hyA As (E1 + E2) hAs hCs Q'
    (by rw [hQlen]; omega)
  rw [hExp1, pairNum_add_expansion, hE1, pairNum_add_expansion, pairNum_single, pairNum_single]
  have hnA : ∀ W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O), classNum (Sum.elim cls cls') (rename Sum.inl A) Q' W = classNum cls A Q' W := fun W => by
    rw [classNum_rename_vars]
    rfl
  have hF3ζ : F3 ζi = f₃ := by rw [hF3, hζi, closureForm_zero]
  have hG3ζ : G3 ζi = g₃ := by rw [hG3, hζi, closureForm_zero]
  have hF3x : F3 xi = liftPairForm M M' (f ⟨k, hk⟩) := by rw [hF3, hxi, closureForm_natAdd, hFV, hki, Fin.append_left]
  have hG3x : G3 xi = liftPairForm M M' (g ⟨k, hk⟩) := by rw [hG3, hxi, closureForm_natAdd, hGV, hki, Fin.append_left]
  simp only [hnA]
  rw [hF3ζ, hG3ζ, hF3x, hG3x]

  have hgen' : ∀ H, (divCycle (pointIdeal O pt1) s H ≠ 0 ∨ divCycle (pointIdeal O pt1) h H ≠ 0) →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ H →
      ∀ i, IsVerticalDivisor H ϖ (cls i - cls' i) (F3 i) (G3 i) := by
    intro H hH hϖH i
    obtain ⟨hf3H, hg3H, haH⟩ := hgen H hH hϖH
    have hPH : pointIdeal O pt1 ≤ H := by
      rcases hH with hH | hH
      · exact (le_and_isRelevant_of_divCycle_ne_zero hH).2.1
      · exact (le_and_isRelevant_of_divCycle_ne_zero hH).2.1
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · obtain rfl : i0 = 0 := Subsingleton.elim _ _
      refine (hv3 _).restrict hPH ?_ ?_
      · rw [hF3, closureForm_zero]
        exact hf3H
      · rw [hG3, closureForm_zero]
        exact hg3H
    · refine (hv3 _).restrict hPH ?_ ?_
      · rw [hF3, closureForm_natAdd]
        have h' := haH (Fin.castAdd (N + n) j)
        rwa [Fin.append_left] at h'
      · rw [hG3, closureForm_natAdd]
        have h' := haH (Fin.natAdd (N + n) j)
        rwa [Fin.append_right] at h'
  have hT3 : pairNum (pointIdeal O pt1) cls cls' F3 G3 E2 Q' =
      cycEval (fun W => if (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W then
          classNum cls A Q' W - classNum cls' A Q' W
        else pairNum W cls cls' F3 G3 Bs₀ Q') (ratDiv (pointIdeal O pt1) s h) := by
    by_cases hm : m = 0
    · have hE20 : E2 = 0 := by
        rw [hE2, hBs₀m hm]
        funext i
        simp
      rw [hE20, pairNum_zero_expansion]
      rw [cycEval_congr_support (n' := fun _ => 0) (fun W _ => ?_), cycEval_zero_fun]
      split_ifs
      · rw [classNum_of_isHomogeneous_zero cls cls' (hm ▸ hA), sub_self]
      · rw [hBs₀m hm, pairNum_zero_expansion]
    · obtain ⟨e', he'⟩ : ∃ e', d + k = e' + 1 := ⟨d + k - 1, by omega⟩
      have hM1' : IsModelOver (pointIdeal O pt1) (e' + 1) := he' ▸ hM1
      rw [hE2, hy', pairNum_mul_pairSum hϖ hM1' cls cls' F3 G3 hv3 ζi xi hBs₀.homogeneous Q'
        (by rw [hQlen]; omega)]
      have hc' : cls' ζi + cls' xi = fun o => (cs o : ℤ) - ch o := by
        rw [hdeg, hcls', hζi, hxi, closureDeg_zero, closureDeg_natAdd, hki, Fin.append_left]
      rw [hc']
      exact pairNum_cut_section hC3 hϖ hM1' cls cls' F3 G3 hv3 hs hh hsP hhP hgen' (by omega) hBs₀ Q'
        (by rw [hQlen]; omega)
  rw [hT3]

  obtain ⟨b3f, b3g, hb3f, hb3g, hb3⟩ := hv₃.degrees
  obtain ⟨bkf, bkg, hbkf, hbkg, hbk⟩ := (hF.vertical ⟨k, hk⟩).degrees
  have hlfk := hliftV (k + 1) ki
  have hFVk : FV ki = f ⟨k, hk⟩ := by rw [hFV, hki, Fin.append_left]
  have hGVk : GV ki = g ⟨k, hk⟩ := by rw [hGV, hki, Fin.append_left]
  rw [hFVk, hGVk] at hlfk
  have hPr : (pointIdeal O pt1).IsPrime := hM1.multiProj.isPrime
  have hmn : ∀ {a b : MRing (bundleIdx (bundleIdx ι M) M') O}, a ∉ pointIdeal O pt1 → b ∉ pointIdeal O pt1 →
      a * b ∉ pointIdeal O pt1 := fun ha hb hab => (hPr.mem_or_mem hab).elim ha hb
  set sT := s * f₃ * liftPairForm M M' (f ⟨k, hk⟩) with hsT_def
  set hT := h * g₃ * liftPairForm M M' (g ⟨k, hk⟩) with hhT_def
  have hsT : IsMultiHomog sT (cs + b3f + vdeg bkf) :=
    IsWeightedHomogeneous.mul (IsWeightedHomogeneous.mul hs hb3f) (isMultiHomog_liftPairForm hbkf)
  have hhT : IsMultiHomog hT (ch + b3g + vdeg bkg) :=
    IsWeightedHomogeneous.mul (IsWeightedHomogeneous.mul hh hb3g) (isMultiHomog_liftPairForm hbkg)
  have hdegT : (fun o => ((cs + b3f + vdeg bkf) o : ℤ) - (ch + b3g + vdeg bkg) o) =
      zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) := by
    funext o
    have h1 := congrFun hdeg o
    have h2 := congrFun hb3 o
    have h3 : ((vdeg bkf o : ℕ) : ℤ) - vdeg bkg o = liftPairDeg (x ⟨k, hk⟩) o - liftPairDeg (x' ⟨k, hk⟩) o := by
      rcases o with _ | _ | j
      · simp [vdeg, liftPairDeg]
      · simp [vdeg, liftPairDeg]
      · have := congrFun hbk j
        simpa [vdeg, liftPairDeg] using this
    simp only [Pi.add_apply, Nat.cast_add, Pi.sub_apply] at h1 h2 ⊢
    linarith
  have hsTP : sT ∉ pointIdeal O pt1 := hmn (hmn hsP hv₃.num_not_mem) hlfk.num_not_mem
  have hhTP : hT ∉ pointIdeal O pt1 := hmn (hmn hhP hv₃.den_not_mem) hlfk.den_not_mem
  have haL : ∀ a : MRing ι O, aeval pt1 (liftPairForm M M' a) = algebraMap Ω Φ (aeval y a) := fun a =>
    aeval_liftPairForm (hpt (k + 1)) a
  have hvT : aeval pt1 sT = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval pt1 hT := by
    simp only [hsT_def, hhT_def, map_mul, hsv, haL, hF.generic, flagLineCoord_flag w w' e hF.sameFlag t k hk, hg₃]
    ring
  have hCk := hCon O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk
  have hc1 := hCk.1 _ _ sT hT hsT hhT hdegT hsTP hhTP hvT
  have hc2 := hCk.2 _ _ s h hs hh hdeg hsP hhP hsv
  have hmemcl : ∀ (c : Fin (1 + (N + n)) → Option (Option K) → ℤ) (μ : Fin (1 + (N + n)) →₀ ℕ)
      (b : Option (Option K) → ℤ), b ∈ classList c μ → ∃ i, c i = b := by
    intro c μ b hb
    unfold classList at hb
    rw [Multiset.mem_toList, Multiset.mem_map] at hb
    obtain ⟨i, -, hi⟩ := hb
    exact ⟨i, hi⟩
  have hvan : ∀ (c : Fin (1 + (N + n)) → Option (Option K) → ℤ) (o : Option (Option K)),
      (∀ i, c i o = 0) → (∀ q : K → ℤ, liftPairDeg q o = 0) →
      ∀ W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O),
        (∀ l : List (Option (Option K) → ℤ), l.length = d + k → (∀ b ∈ l, b o = 0) → vNumL W l = 0) →
        classNum c A Q' W = 0 := by
    intro c o hc hq W hW
    unfold classNum
    refine Finset.sum_eq_zero fun μ hμ => ?_
    rw [hW _ ?_ ?_, mul_zero]
    · rw [List.length_append, classList_length_of_mem_support _ hA hμ, hQlen]
      omega
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨i, rfl⟩ := hmemcl c μ b hb
        exact hc i
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hb
        exact hq q
  have hclsn : ∀ i, cls i none = 0 := by
    intro i
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · obtain rfl : i0 = 0 := Subsingleton.elim _ _
      rw [hcls, closureDeg_zero]
      rfl
    · rw [hcls, closureDeg_natAdd]
      rfl
  have hcls'n : ∀ i, cls' i (some none) = 0 := by
    intro i
    refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
    · obtain rfl : i0 = 0 := Subsingleton.elim _ _
      rw [hcls', closureDeg_zero]
      rfl
    · rw [hcls', closureDeg_natAdd]
      rfl
  have hnA0 : ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W →
      ratDiv (pointIdeal O pt1) sT hT W ≠ 0 → classNum cls A Q' W = 0 := fun W hϖW hW =>
    hvan cls none hclsn (fun _ => rfl) W (hc1 W hϖW hW)
  have hnA'0 : ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W →
      ratDiv (pointIdeal O pt1) s h W ≠ 0 → classNum cls' A Q' W = 0 := fun W hϖW hW =>
    hvan cls' (some none) hcls'n (fun _ => rfl) W (hc2 W hϖW hW)

  have hrT : ratDiv (pointIdeal O pt1) sT hT = ratDiv (pointIdeal O pt1) s h + ratDiv (pointIdeal O pt1) f₃ g₃ +
      ratDiv (pointIdeal O pt1) (liftPairForm M M' (f ⟨k, hk⟩)) (liftPairForm M M' (g ⟨k, hk⟩)) := by
    rw [hsT_def, hhT_def, ratDiv_mul (hmn hsP hv₃.num_not_mem) (hmn hhP hv₃.den_not_mem)
      hlfk.num_not_mem hlfk.den_not_mem, ratDiv_mul hsP hhP hv₃.num_not_mem hv₃.den_not_mem]
  have hfs := ratDiv_finite_support (pointIdeal O pt1) s h
  rw [← cycEval_add_cycle (ratDiv_finite_support _ _ _) (ratDiv_finite_support _ _ _)]
  have hsum : ratDiv (pointIdeal O pt1) f₃ g₃ +
      ratDiv (pointIdeal O pt1) (liftPairForm M M' (f ⟨k, hk⟩)) (liftPairForm M M' (g ⟨k, hk⟩)) =
      ratDiv (pointIdeal O pt1) sT hT - ratDiv (pointIdeal O pt1) s h := by
    rw [hrT]
    abel
  rw [hsum, ← cycEval_sub_cycle _ _ _ (ratDiv_finite_support _ _ _) hfs]
  set n' : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O) → ℤ := fun W =>
    if (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W then 0 else classNum cls A Q' W with hn'
  have e1a : cycEval (fun W => classNum cls A Q' W) (ratDiv (pointIdeal O pt1) sT hT) =
      cycEval n' (ratDiv (pointIdeal O pt1) sT hT) := by
    refine cycEval_congr_support fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W
    · simp only [hn', if_pos hϖW]
      exact hnA0 W hϖW hW
    · simp only [hn', if_neg hϖW]
  have e1b : cycEval n' (ratDiv (pointIdeal O pt1) sT hT) = cycEval n' (ratDiv (pointIdeal O pt1) s h) := by
    refine cycEval_congr_cycle fun W => ?_
    by_cases hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W
    · simp only [hn', if_pos hϖW, mul_zero]
    · have h3 : ratDiv (pointIdeal O pt1) f₃ g₃ W = 0 := by
        by_contra hne
        exact hϖW (hv₃.vertical W hne)
      have h4 : ratDiv (pointIdeal O pt1) (liftPairForm M M' (f ⟨k, hk⟩)) (liftPairForm M M' (g ⟨k, hk⟩)) W = 0 := by
        by_contra hne
        exact hϖW (hlfk.vertical W hne)
      rw [hrT]
      simp only [Pi.add_apply, h3, h4, add_zero]
  rw [e1a, e1b, ← cycEval_sub_fun _ _ _ hfs, ← cycEval_add_fun _ _ _ hfs]
  set G : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O) → ℤ := fun W =>
    if (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W then 0 else pairNum W cls cls' F3 G3 Bs₀ Q' with hG
  have e2 : cycEval (fun W => n' W - classNum cls A Q' W +
      if (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W then classNum cls A Q' W - classNum cls' A Q' W
      else pairNum W cls cls' F3 G3 Bs₀ Q') (ratDiv (pointIdeal O pt1) s h) =
      cycEval G (ratDiv (pointIdeal O pt1) s h) := by
    refine cycEval_congr_support fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W
    · rw [hn', hG]
      simp only [if_pos hϖW]
      have := hnA'0 W hϖW hW
      linarith
    · rw [hn', hG]
      simp only [if_neg hϖW]
      ring
  rw [e2]

  unfold cycEval
  rw [finsum_eq_single _ (pointIdeal O pt0) ?_]
  · by_cases hk0 : k = 0
    · rw [if_pos hk0]
      by_cases hϖ0 : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ pointIdeal O pt0
      · simp only [hG, if_pos hϖ0, mul_zero]
      · rw [hdiv _ hϖ0, if_neg (by omega), zero_mul]
    · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
      have hM0 : IsModelOver (pointIdeal O pt0) (d + (k - 1)) := (hModk k hk0' hk.le).1
      have hϖ0 : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ pointIdeal O pt0 := fun h' => by
        have h'' : ϖ ∈ (pointIdeal O pt0).comap (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := h'
        rw [hM0.noTorsion, Ideal.mem_bot] at h''
        exact hϖ.ne_zero h''
      rw [if_neg hk0, hdiv _ hϖ0, if_pos ⟨hk0', rfl⟩, one_mul, hG]
      simp only [if_neg hϖ0]
      have hPr0 : (pointIdeal O pt0).IsPrime := hM0.multiProj.isPrime
      obtain ⟨hv₂, hg₂⟩ := h₂ hk0'
      obtain ⟨hf30, hg30, hval30⟩ := h₃0 hk0'
      have h32 : ratDiv (pointIdeal O pt0) f₃ g₃ = ratDiv (pointIdeal O pt0) f₂ g₂ := by
        obtain ⟨b2, b2', hb2, hb2', hb2d⟩ := hv₂.degrees
        refine ratDiv_eq_of_sub_mem hf30 hg30 hv₂.num_not_mem hv₂.den_not_mem
          (cross_mem hb3f hb3g hb2 hb2' (fun o => ?_) hval30 hg₂)
        rw [congrFun hb3 o, congrFun hb2d o]
      have hv2 : ∀ i, IsVerticalDivisor (pointIdeal O pt0) ϖ (cls i - cls' i) (closureForm M M' f₂ FV i)
          (closureForm M M' g₂ GV i) := by
        intro i
        refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
        · obtain rfl : i0 = 0 := Subsingleton.elim _ _
          rw [closureForm_zero, closureForm_zero, hcls, hcls', closureDeg_zero, closureDeg_zero]
          exact hv₂
        · rw [closureForm_natAdd, closureForm_natAdd]
          exact hliftV k j
      rw [pairNum_congr_ratDiv (F' := closureForm M M' f₂ FV) (G' := closureForm M M' g₂ GV) (fun i => ?_) Bs₀ Q']
      · exact hExp O ϖ hϖ _ _ (pointIdeal O pt0) (d + (k - 1)) hM0 _ cls cls' _ _ hv2 m A hA Bs₀ Bs hBs₀ hBs Q'
          (by rw [hQlen]; omega)
      · refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
        · obtain rfl : i0 = 0 := Subsingleton.elim _ _
          rw [hF3, hG3, closureForm_zero, closureForm_zero, closureForm_zero, closureForm_zero]
          exact h32
        · rw [hF3, hG3, closureForm_natAdd, closureForm_natAdd, closureForm_natAdd, closureForm_natAdd]
  · intro W hW
    by_cases hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W
    · rw [hG]
      simp only [if_pos hϖW, mul_zero]
    · rw [hdiv W hϖW, if_neg (fun h' => hW h'.2), zero_mul]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
