import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def projOfForms {e r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w j := if h : (j : ℕ) < r then ∑ t, (L ⟨j, h⟩ t : ℂ) * w t else 0
  map_add' := by
    intro w w'
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c w
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [Finset.mul_sum, mul_left_comm]

theorem isGoodProj_of_intOver {P : Ideal (MRing ι)} (hK : Nonempty K) (hhom : IsMultiHomogIdeal P)
    {e r : ℕ} (hr : r ≤ e + 1) (L : Fin r → ((k : K) → ι k) → ℚ)
    (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t)) :
    IsGoodProj P (projOfForms (e := e) L) := by
  intro z hz hΨ
  obtain ⟨k0⟩ := hK
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hv : ∀ t, evQ P _ hzc (segQ P t) = c * segre z t := by
      intro t
      rw [segQ, evQ_mk, segMon, eval₂_prod]
      simp only [eval₂_X, scaleBlock, Finset.prod_mul_distrib, segre]
      congr 1
      simp
    have hforms : ∀ j, evQ P _ hzc (forms (segQ P) L j) = 0 := by
      intro j
      have hΨj := congrFun hΨ ⟨j.1, by omega⟩
      simp only [projOfForms, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta,
        Pi.zero_apply] at hΨj
      simp only [forms, map_sum, map_rat_smul, hv, Rat.smul_def]
      rw [show ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t by
        rw [Finset.mul_sum]; congr 1; funext t; ring, hΨj, mul_zero]
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) :
          MvPolynomial (Fin r) ℚ →+* _) = g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        simp [g0, hforms]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, hv, map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

theorem evalAlgHom_comp_aeval_forms {F : Type} (Q : F → Ideal (MRing ι))
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) (W : F) :
    (Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal (Q W)) W).comp
        (aeval (forms (fun t W => segQ (Q W) t) L)) = aeval (forms (segQ (Q W)) L) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [forms]

theorem divPushCommonProj : DivPushCommonProjStatement := by
  intro K _ ι _ P n A s hP hs
  classical
  let F := ((divSupp_finite P s).subset (fun _ h => h.1) :
    {W' | W' ∈ divSupp P s ∧ IsHorizontal W'}.Finite).toFinset
  have hAr : ∀ W : F, IsArithVar W.1 (n + 1) := fun W => by
    have h := W.2
    rw [Set.Finite.mem_toFinset] at h
    exact (divSuppArith K ι P (n + 1) A s W.1 hP hs h.1).1 h.2
  let v : ((k : K) → ι k) → ∀ W : F, MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1 :=
    fun t W => segQ W.1 t
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) v (n + 1) (by
    intro r L hrL hind
    have hW : ∀ W : F, ∃ p : MvPolynomial (Fin r) ℚ,
        aeval (forms (segQ W.1) L) p = 0 ∧ p ≠ 0 := by
      intro W
      have h := forms_not_algebraicIndependent W.1 n (hAr W) hrL L
      rw [algebraicIndependent_iff] at h
      push Not at h
      exact h
    choose G hG0 hGne using hW
    have hQ : (∏ W : F, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hGne W
    refine hQ ((algebraicIndependent_iff.mp hind) _ ?_)
    funext W
    have h1 := DFunLike.congr_fun (evalAlgHom_comp_aeval_forms (fun W : F => W.1) L W) (∏ W : F, G W)
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at h1
    rw [Pi.zero_apply]
    refine h1.trans ?_
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ W) (hG0 W))
  refine ⟨projOfForms L, fun W hW hH => ?_⟩
  have hWF : W ∈ F := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hW, hH⟩
  have hA := hAr ⟨W, hWF⟩
  refine isGoodProj_of_intOver hA.1 hA.2.1.2.1 hr L fun t => ?_
  obtain ⟨p, hpm, hp⟩ := hL t
  refine ⟨p, hpm, ?_⟩
  have h1 := congrArg
    ((Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1) ⟨W, hWF⟩ :
      (∀ W : F, MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1) →+* MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W)) hp
  rw [Polynomial.hom_eval₂, map_zero, ← AlgHom.comp_toRingHom,
    evalAlgHom_comp_aeval_forms (fun W : F => W.1) L ⟨W, hWF⟩] at h1
  exact h1

end

end ReciprocityTheory.ChartRestriction.G.Geo
