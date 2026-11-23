import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def tensorPowH (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  | 0 => A
  | n + 1 => (tensorPowH A n).tensor A

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) : (tensorPowH A n).a = fun k => ((n + 1 : ℕ) : ℤ) * A.a k := by
  induction n with
  | zero => funext k; simp [tensorPowH]
  | succ n ih =>
    funext k
    show (tensorPowH A n).a k + A.a k = _
    rw [ih]
    push_cast
    ring

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) (z : (Σ k, ι k) → ℂ) : (tensorPowH A n).h z = A.h z ^ (n + 1) := by
  induction n with
  | zero => simp [tensorPowH]
  | succ n ih =>
    show (tensorPowH A n).h z * A.h z = _
    rw [ih, pow_succ _ (n + 1)]

theorem isSmoothHerm_tensorPowH {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (n : ℕ) : IsSmoothHerm (tensorPowH A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact isSmoothHerm_tensor ih hA

theorem update_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin n) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    (t : ℕ) :
    I K ι P n (Function.update L j (tensorPowH A t)) = ((t + 1 : ℕ) : ℝ) * I K ι P n (Function.update L j A) := by
  induction t with
  | zero => simp [tensorPowH]
  | succ t ih =>
    have h := GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem.multilin_of_isFamily hI K ι P n L j
      (tensorPowH A t) A hP hL (isSmoothHerm_tensorPowH hA t) hA
    show I K ι P n (Function.update L j ((tensorPowH A t).tensor A)) = _
    rw [h, ih]
    push_cast
    ring

theorem const_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (t : ℕ) :
    I K ι P n (fun _ => tensorPowH A t) = ((t + 1 : ℕ) : ℝ) ^ n * I K ι P n (fun _ => A) := by
  classical
  let Lr : ℕ → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun r i => if (i : ℕ) < r then tensorPowH A t else A
  have hLr : ∀ r j, IsSmoothHerm (Lr r j) := fun r j => by
    simp only [Lr]
    split_ifs
    · exact isSmoothHerm_tensorPowH hA t
    · exact hA
  have step : ∀ r, r ≤ n → I K ι P n (Lr r) = ((t + 1 : ℕ) : ℝ) ^ r * I K ι P n (Lr 0) := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro hr
      let j : Fin n := ⟨r, hr⟩
      have e1 : Lr (r + 1) = Function.update (Lr r) j (tensorPowH A t) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · have : (i : ℕ) ≠ r := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi]
          simp only [Lr]
          congr 1
          exact propext ⟨fun h => by omega, fun h => by omega⟩
      have e2 : Lr r = Function.update (Lr r) j A := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · rw [Function.update_of_ne hi]
      rw [e1, update_tensorPowH hI hP (hLr r) j hA t, ← e2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  have e3 : Lr n = fun _ => tensorPowH A t := by funext i; simp [Lr, i.2]
  have e4 : Lr 0 = fun _ => A := by funext i; simp [Lr]
  rw [e3, e4] at hn
  exact hn

omit [∀ k, Fintype (ι k)] in

theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {m N : ℕ} {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hv : ∀ j, v j ∈ chartLat y A.a m) : blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ ⟨oldV N p, oldV N q, by simp [oldV, hpq], rfl⟩

end PowerBlockTop

open PowerBlockTop in

theorem PowerBlockTop.proof (hPF : PFCoordStatement) (hIso : IsomInvariance.Statement)
    (hAB : AddBlockIsometric.Statement) : PowerBlockTop.Statement := by
  classical
  intro K _ _ ι _ Ω _ _ y D A m N v B I hI hy hA hm hv hgen hBa hBs hmet

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  have hFn := blockFnField_addBlock c hc hv
  have hbm := isBlockMap_oldV (ι := ι) N
  have hyv : IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) :=
    CoordArithOfFnField.proof K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
      (fun k => by
        cases k with
        | none => exact ⟨j₀, hj₀⟩
        | some k => exact ⟨c k, hc k⟩) hFn.symm hy
  have hcomp : addBlock y v ∘ oldV N = y := rfl
  have himg : imageZ (oldV N) (mCoordIdeal (addBlock y v)) = mCoordIdeal y := by
    rw [GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) hbm,
      hcomp]
  have hAm : IsSmoothHerm (tensorPowH A (m - 1)) := isSmoothHerm_tensorPowH hA _
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpull := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hbm (tensorPowH A (m - 1))

  have hPFe := hPF I hI K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) (D + 1)
    (fun _ => tensorPowH A (m - 1)) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1)))
    hbm hyv (by rw [himg]; exact hy) (fun _ => hAm) (fun _ => hpull)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hcomp, hFn]), Nat.cast_one, one_mul, himg] at hPFe

  have hiso : ∀ _ : Fin (D + 1), IsIsometricOn (mCoordIdeal (addBlock y v)) B
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) := fun _ =>
    hAB K ι Ω y D A m N v B _ hy hm hv hgen hBa
      (by
        show pullDeg some (tensorPowH A (m - 1)).a = _
        rw [tensorPowH_a, hm'])
      (fun z => by
        show (tensorPowH A (m - 1)).h (fun p => z (oldV N p)) = _
        rw [tensorPowH_h, hm']
        rfl) hmet
  have e1 := hIso (Option K) (addIdx ι N) (I (Option K) (addIdx ι N)) (hI _ _) (mCoordIdeal (addBlock y v)) (D + 1)
    (fun _ => B) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) hyv (fun _ => hBs)
    (fun _ => GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hbm hpull hAm) hiso
  rw [e1, hPFe, const_tensorPowH hI hy hA, hm']

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
