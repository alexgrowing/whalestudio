import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMonomialShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbMonomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis hermZpow hermLine_eq_of isSmoothHerm_tensor
  isSmoothHerm_hermZpow fam_update_eq_snoc fam_snoc_zpow isSmoothHerm_ofMetrics_fs)

noncomputable section

set_option linter.unusedSectionVars false

section Scaling

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zcomb_eq_tensor (A X : HermLine ι) (q : ℕ) :
    HermLine.zcomb A X q 1 = (hermZpow A q).tensor X :=
  hermLine_eq_of (by funext k; simp [HermLine.zcomb, HermLine.tensor, hermZpow])
    (by funext z; simp [HermLine.zcomb, HermLine.tensor, hermZpow])

theorem isSmoothHerm_zcomb {A X : HermLine ι} (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A X q 1) := by
  rw [zcomb_eq_tensor]
  exact isSmoothHerm_tensor (isSmoothHerm_hermZpow hA q) hX

theorem isConjInvariantH_zcomb {A B : HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) (p q : ℤ) :
    IsConjInvariantH (HermLine.zcomb A B p q) := by
  intro z
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem isConjInvariantH_fsH : IsConjInvariantH (fsH ι) := by
  intro z
  simp [fsH, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem fam_update_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    I P (n + 1) (Function.update L a (HermLine.zcomb A X q 1)) =
      q * I P (n + 1) (Function.update L a A) + I P (n + 1) (Function.update L a X) := by
  rw [zcomb_eq_tensor]
  have hAq := isSmoothHerm_hermZpow hA (q : ℤ)
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAq hX), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hX, hI.2.1 P n _ _ _ hP hR hAq hX, fam_snoc_zpow hI hP _ hR hA (q : ℤ)]
  push_cast
  ring

theorem fam_eq_famExt_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (t j) 1) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis ![X, A] t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (w : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then w else F (t j)) =
          Function.update (fun j => if j ∈ T then w else F (t j)) a w := by
      intro β w F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (w : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then w else F (t j)) a (F i) =
          fun j => if j ∈ T then w else F (Function.update t a i j) := by
      intro β w F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact isSmoothHerm_zcomb hA hX q
      · exact hsm (t j)
    have eL : (fun j => if j ∈ insert a T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
        Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a
          (HermLine.zcomb A X q 1) :=
      hins _ _
    have eV : (fun j => if j ∈ insert a T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) =
        Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
          ![1, (q : ℝ)] :=
      hins (![1, (q : ℝ)] : Fin 2 → ℝ) fun i => Pi.single i 1
    have hA1 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a A =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 1 j) :=
      hupd _ ![X, A] 1
    have hX0 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a X =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 0 j) :=
      hupd _ ![X, A] 0
    have hV1 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 1 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 1 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1
    have hV0 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 0 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 0 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0
    have hw : (![1, (q : ℝ)] : Fin 2 → ℝ) = (q : ℝ) • Pi.single 1 1 + (1 : ℝ) • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, fam_update_zcomb hI hP _ hL a hA hX q, hA1, hX0, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw,
      MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, hV1, hV0,
      smul_eq_mul, smul_eq_mul]
    ring

theorem tendsto_fam_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) :
    Tendsto (fun q : ℕ => I P (n + 1) (fun _ => HermLine.zcomb A X q 1) / (q : ℝ) ^ (n + 1)) atTop
      (𝓝 (I P (n + 1) (fun _ => A))) := by
  have hfull : ∀ q : ℕ, I P (n + 1) (fun _ => HermLine.zcomb A X q 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) := by
    intro q
    simpa using fam_eq_famExt_zcomb hI hP hA hX q Finset.univ (fun _ => 0)
  have hscale : ∀ q : ℕ, q ≠ 0 → famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) / (q : ℝ) ^ (n + 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1]) := by
    intro q hq
    have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have e : (fun _ : Fin (n + 1) => (![1, (q : ℝ)] : Fin 2 → ℝ)) =
        fun i => (fun _ : Fin (n + 1) => (q : ℝ)) i • (![1 / (q : ℝ), 1] : Fin 2 → ℝ) := by
      funext i j
      fin_cases j <;> simp [hq']
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hlim : Tendsto (fun q : ℕ => famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1])) atTop
      (𝓝 (famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]))) := by
    simp only [famExt_apply]
    refine tendsto_finsetSum _ fun s _ => Tendsto.const_mul _ (tendsto_finsetProd _ fun j _ => ?_)
    generalize s j = i
    fin_cases i
    · simpa using (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0))
    · simp
  have hval : famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]) = I P (n + 1) (fun _ => A) := by
    have e : (fun _ : Fin (n + 1) => (![0, 1] : Fin 2 → ℝ)) = fun j => Pi.single ((fun _ => (1 : Fin 2)) j) 1 := by
      funext j i
      fin_cases i <;> simp
    rw [e, famExt_basis]
    rfl
  rw [hval] at hlim
  refine hlim.congr' ((eventually_ge_atTop 1).mono fun q hq => ?_)
  dsimp only
  rw [hfull, hscale q (by omega)]

end Scaling

theorem ArithmeticVolumeNef.proof (hS : MonomialShift.Statement) (hPM : PerturbMonomial.Statement)
    (hU : UpperNormalisation.Statement) : ArithmeticVolumeNef.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II hD hII hY hbir ha hP0 hsemi hmon hconj
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  let f : ℕ → ℝ := fun τ =>
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F)
  show limsup f atTop ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hcnt : ∀ (B : HermLine ι) (La : ℕ → AddSubgroup Ω) (τ : ℕ),
      0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B) La τ := fun B La τ => by
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hf0 : ∀ τ, 0 ≤ f τ := fun τ => div_nonneg (hcnt _ _ _) (div_nonneg (by positivity) hFpos.le)

  have key : ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → limsup f atTop ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) + ε) / (q : ℝ) ^ (D + 1) := by
    intro q hq ε hε
    set B := HermLine.zcomb A (fsH ι) q 1 with hBdef
    set c := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε with hc
    have hsg : IsSmallGeneratedDatum P0 y D B := hPM K ι Ω y D a A P0 q hD hY hbir ha hP0 hsemi hmon hq
    have hBconj : IsConjInvariantH B := isConjInvariantH_zcomb hconj isConjInvariantH_fsH _ _
    have hBa : ∀ k, 1 ≤ B.a k := by
      intro k
      simp only [hBdef, HermLine.zcomb, fsH, HermLine.ofMetrics, ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.one_apply, mul_one]
      nlinarith [show (0 : ℤ) ≤ (q : ℤ) * (a k : ℤ) by positivity]
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hU K ι Ω y D B P0 II hD hII hY hbir hsg hBconj hBa ε hε)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hbound : ∀ᶠ τ : ℕ in atTop, f τ ≤ c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) := by
      filter_upwards [eventually_ge_atTop (q * N + 1)] with τ hτ
      have hτpos : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
      have hdm := Nat.div_add_mod τ q
      have hmod := Nat.mod_lt τ (show 0 < q by omega)
      have hqn : τ ≤ q * (τ / q + 1) := by rw [Nat.mul_add, mul_one]; omega
      have hnN : N ≤ τ / q + 1 := by
        have : N ≤ τ / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
        omega
      have hnq : (((τ / q + 1 : ℕ) : ℝ)) * q ≤ τ + q := by
        have := Nat.div_mul_le_self τ q
        have h' : (τ / q + 1) * q ≤ τ + q := by rw [Nat.add_mul, one_mul]; omega
        exact_mod_cast h'
      have h1 : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
          c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) :=
        (hS K ι Ω y D a A P0 q τ (τ / q + 1) hY hbir ha hP0 hsemi hmon hq hqn).trans (hN _ hnN)
      have hc0 : 0 ≤ c := by
        have hpos : 0 < (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F := by positivity
        exact (mul_nonneg_iff_of_pos_right hpos).mp ((hcnt _ _ _).trans h1)
      have hnle : (((τ / q + 1 : ℕ) : ℝ)) ≤ (τ + q) / q := by rw [le_div_iff₀ hqpos]; exact hnq
      have h2 : (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) ≤ ((τ + q) / q) ^ (D + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hnle _
      have e : c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) =
          c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) / ((τ : ℝ) ^ (D + 1) / F) := by
        rw [show (1 : ℝ) + q / τ = (τ + q) / τ by field_simp]
        simp only [div_pow]
        field_simp
      show smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F) ≤ _
      rw [e, div_le_div_iff_of_pos_right (by positivity)]
      calc _ ≤ c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) := h1
        _ ≤ c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) := by gcongr
    have hlim : Tendsto (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop
        (𝓝 (c / (q : ℝ) ^ (D + 1))) := by
      have h0 : Tendsto (fun τ : ℕ => (q : ℝ) / τ) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (c / (q : ℝ) ^ (D + 1))
    calc limsup f atTop ≤ limsup (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop :=
          limsup_le_limsup hbound (isCoboundedUnder_le_of_le atTop hf0) hlim.isBoundedUnder_le
      _ = c / (q : ℝ) ^ (D + 1) := hlim.limsup_eq

  have hT := tendsto_fam_zcomb (hII K ι) hY hsemi.1 (show IsSmoothHerm (fsH ι) from isSmoothHerm_ofMetrics_fs 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ q : ℕ in atTop, limsup f atTop - ε ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) / (q : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hk := key q hq ε hε
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
    have hεq : ε / (q : ℝ) ^ (D + 1) ≤ ε := div_le_self hε.le hq1
    rw [add_div] at hk
    linarith
  have := ge_of_tendsto hT hev
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
