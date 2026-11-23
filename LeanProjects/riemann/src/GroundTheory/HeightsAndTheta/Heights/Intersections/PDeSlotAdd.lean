import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_eq_zero_of_vanish (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem ptsIntegral_update_tensor (hE : ResExistsStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) {L : Fin e → HermLine ι} (j : Fin e) {M N A : HermLine ι}
    {s : MRing ι} (hL : ∀ i, IsSmoothHerm (L i)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot (Function.update L j (M.tensor N))) (logNorm A s) =
      ptsIntegral P (pot (Function.update L j M)) (logNorm A s) +
        ptsIntegral P (pot (Function.update L j N)) (logNorm A s) := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by have := j.pos; omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set T : Fin m → HermLine ι := fun i => L (Equiv.swap 0 j i.succ) with hT
  have hT' : ∀ i, IsSmoothHerm (T i) := fun i => hL _
  have hU : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
    intro X hX i
    rcases eq_or_ne i j with rfl | h
    · simpa using hX
    · rw [Function.update_of_ne h]
      exact hL i
  have hC : ∀ X : HermLine ι, IsSmoothHerm X →
      ∀ i, IsSmoothHerm ((Fin.cons X T : Fin (m + 1) → HermLine ι) i) :=
    fun X hX i => Fin.cases hX hT' i
  have key : ∀ X : HermLine ι, IsSmoothHerm X →
      ptsIntegral P (pot (Function.update L j X)) (logNorm A s) =
        mInt R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
          (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [ptsIntegral_eq_mInt' hE resBridge R hP (hU X hX) hA hs, ← potOf_cons R X T,
      ← mIntSymm R.A (fun i => potOf R (Function.update L j X i)) (Equiv.swap 0 j)]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, hT, Function.update_of_ne hne]
  rw [key _ (isSmoothHerm_tensor hM hN), key M hM, key N hN]
  have hΦ : ∀ i, IsPotential R.A (potOf R (T i)) := fun i => isPotential_potOf R (hT' i)
  have hPM := isPotential_potOf R hM
  have hPN := isPotential_potOf R hN
  have e1 : mInt R.A (Fin.cons (potOf R (M.tensor N)) fun i => potOf R (T i))
      (fun x => logNorm A s (R.lift x x)) =
      mInt R.A (Fin.cons (potOf R M + potOf R N) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr _ (locDens_cons_congr _ _ fun j y hy =>
      germ_of_eqOn R (fun x z hz => ?_) j y hy) fun _ => rfl
    have hm := (R.mem x z hz).1
    show Real.log (M.h (R.lift x z) * N.h (R.lift x z)) =
      Real.log (M.h (R.lift x z)) + Real.log (N.h (R.lift x z))
    exact Real.log_mul (M.pos _ hm).ne' (N.pos _ hm).ne'
  have hI : ∀ X : HermLine ι, IsSmoothHerm X →
      MIntegrable R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [← potOf_cons R X T]
    exact brIntegrable R _ A s hP (hC X hX) hA hs
  rw [e1]
  exact mIntAdd R.A _ _ _ hPM hPN hΦ _ (hI M hM) (hI N hN)

theorem DeSlotAdd.proof (hE : ResExistsStatement) : DeSlotAdd.Statement := by
  intro K _ ι _ P n L j M N A A' s s' hP hL hM hN hA hA' hs hs' _

  have hZ : ∀ (B C : HermLine ι) (t : MRing ι), IsSmoothHerm B → IsSmoothHerm C →
      IsSectionOn P C t →
      ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j (M.tensor N))))
          (logNorm C t) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j M)))
            (logNorm C t) +
          ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j N)))
            (logNorm C t) := by
    intro B C t hB hC ht
    have hc : ∀ X : HermLine ι,
        (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j X)) :
          Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
          pot (Function.update (Fin.cons B L : Fin (n + 1) → HermLine ι) j.succ X) := by
      intro X
      rw [← Fin.cons_update]
      funext i
      exact Fin.cases rfl (fun i => rfl) i
    rw [hc, hc, hc]
    exact ptsIntegral_update_tensor hE hP j.succ (fun i => Fin.cases hB hL i) hM hN hC ht

  have hW : ∀ (t t' : MRing ι) (C C' : HermLine ι), IsSectionOn P C t → IsSmoothHerm C' →
      IsSectionOn P C' t' →
      (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t')) =
        (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t')) +
          (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')) := by
    intro t t' C C' ht hC' ht'
    have hfin : {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
      (divSupp_finite P t).subset fun W hW => hW.1
    have hpt : ∀ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W},
        (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
          (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
            (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j N)) (logNorm C' t') := by
      intro W hW
      rw [← mul_add]
      congr 1
      have hWa : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) C t W hP ht hW.1).1 hW.2
      by_cases hsW : t' ∈ W
      · have h0 : ∀ z ∈ mcPts W, logNorm C' t' z = 0 := by
          intro z hz
          simp [logNorm, hz.2 t' hsW]
        rw [ptsIntegral_eq_zero_of_vanish W _ h0, ptsIntegral_eq_zero_of_vanish W _ h0,
          ptsIntegral_eq_zero_of_vanish W _ h0, add_zero]
      · obtain ⟨a, ha, hta, -⟩ := ht'
        exact ptsIntegral_update_tensor hE hWa j hL hM hN hC' ⟨a, ha, hta, hsW⟩
    show ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
        ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
          ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')
    rw [← finsum_mem_add_distrib hfin]
    exact finsum_mem_congr rfl hpt
  unfold De
  rw [hW s s' A A' hs hA' hs', hW s' s A' A hs' hA hs, hZ A' A s hA' hA hs, hZ A A' s' hA hA' hs']
  ring

end GroundTheory.Heights₂.Heights.Inter
