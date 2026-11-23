import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpUnif
import Formalism.SharpRestriction.CuspSpanNormBounds.SLemOm
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

theorem hsNormSq_nonneg' {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  simp only [hsNormSq, hsInner]
  rw [Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => by
    simpa using (inner_self_nonneg (𝕜 := ℂ) (x := A ((stdOrthonormalBasis ℂ Wq) i))))

theorem ell_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    ell k r z (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = 0 := by
  simp only [inWb] at hz
  simp only [ell, eI]
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro heq
    have h' := congrArg Fin.val heq
    simp [eI] at h'
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [a.isLt]))

theorem psi_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) :
    psi k r z c (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = 1 := by
  simp only [psi]
  simp [ell_one hz]

theorem Gf_big {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hsec : IsSection k r z z' μsec)
    (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (ζ : ℂ) (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    0 < Gf k r z z' (bigCell k r c (μsec ζ)) := by
  have h1 := (Formalism.MainNotions.InterlacingSignCuts.bigCell_D k r z z' hz hz' c hc (μsec ζ)).2
  rw [(hsec.2 ζ hζ).2] at h1
  have h2 := (Formalism.QuantumDeterminants.bigCellMinors k r z z' c (μsec ζ) hz hz').1 (Fin.last r)
  simp only [Fin.val_last] at h2
  have hne : (∏ a : Fin r with a.val < r, c a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have e : Gf k r z z' (bigCell k r c (μsec ζ)) =
      Complex.normSq (∏ a : Fin r with a.val < r, c a) * (Complex.normSq ζ - Tz k r z * Tz k r z') := by
    unfold Gf
    rw [h1, h2, Complex.normSq_mul]
    ring
  rw [e]
  exact mul_pos (Complex.normSq_pos.2 hne) (by linarith)

theorem bcWeight_ne {k r : ℕ} (hk : 2 ≤ k) {T T' : ℝ} {p : (Fin r → ℂ) × ℂ} (h : bcWeight k r T T' p ≠ 0) :
    (∀ a, p.1 a ≠ 0) ∧ T * T' < Complex.normSq p.2 := by
  simp only [bcWeight] at h
  split_ifs at h with hle
  · have h1 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    refine ⟨fun a => ?_, ?_⟩
    · have ha := Finset.prod_ne_zero_iff.mp h1 a (Finset.mem_univ a)
      have hexp : 2 * (Mdim k r a - 2) ≠ 0 := by
        simp only [Mdim]
        omega
      intro h0
      apply ha
      rw [h0, norm_zero, zero_pow hexp]
    · have hne : Complex.normSq p.2 - T * T' ≠ 0 := by
        intro h0
        apply h2
        rw [h0]
        exact zero_pow (by omega)
      exact lt_of_le_of_ne hle (fun heq => hne (by rw [heq]; ring))
  · exact absurd rfl h

theorem big_cell_eq : BigCellEq := by
  intro D τ w w' θ W hW lam' A hA hT hT' f hfEq μsec hsec
  have hW' := hW
  obtain ⟨-, -, hz, hz', hTz, hTz', hG, -, -, -, -, -, -, -⟩ := hW'
  have hk2 : 2 ≤ D.R.k := by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega
  unfold jNorm2 MMv jNormSq
  rw [show (toBessel D τ w w' θ W lam' A hW hA hT hT').z = W.z from rfl,
    show (toBessel D τ w w' θ W lam' A hW hA hT hT').z' = W.z' from rfl, hTz, hTz']
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight D.R.k D.R.rS (Tr D w) (Tr D w') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := bcWeight_ne hk2 hw0
  congr 2
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hsNormSq_nonneg' _)]
  congr 1

  set g := bigCell D.R.k D.R.rS q.1 (μsec q.2) with hgdef
  have hζ' : Tz D.R.k D.R.rS W.z * Tz D.R.k D.R.rS W.z' < Complex.normSq q.2 := by rw [hTz, hTz']; exact hζ
  have hμ := (hsec.2 q.2 hζ').1
  have hgU : g ∈ UH (Hpk D.R.k D.R.rS) := Formalism.QuantumDeterminants.bigCellMem _ _ _ _ hc hμ
  have hGp := Gf_big hz hz' hsec q.1 hc q.2 hζ'
  have hRS := Formalism.MainNotions.S.Lem.orbRStabBig _ _ _ _ hc hμ
  have hgi : g⁻¹ * g = 1 := by
    have hu := WeylGroupFacts.isUnit_of_uh hgU
    exact Matrix.nonsing_inv_mul _ hu
  set one : Mt D.R.k D.R.rS := fun i j => (1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j
    with hone
  have hof : (Matrix.of one : Matrix _ _ ℂ) = 1 := rfl
  have hRel : IsRelStab (toBessel D τ w w' θ W lam' A hW hA hT hT') g := by
    intro a ha
    rw [hRS] at ha
    rw [Set.mem_singleton_iff.1 ha, Matrix.mul_one, hgi]
    show psi _ _ W.z _ 1 = psi _ _ W.z' _ 1
    rw [psi_one hz, psi_one hz']
  have hHaar : IsHaarOn (RStab D.R.k D.R.rS g) (Measure.dirac one) := by
    refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · have hset : {x : Mt D.R.k D.R.rS | Matrix.of x ∉ ({1} : Set (Matrix _ _ ℂ))} = {one}ᶜ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_compl_iff]
        refine not_congr ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
        funext i j
        exact congrFun (congrFun h i) j
      rw [hRS, hset, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
      simp
    · intro s hs
      rw [hRS] at hs
      rw [Set.mem_singleton_iff.1 hs]
      have hl1 : lmulM (k := D.R.k) (r := D.R.rS) (1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) = id := by
        funext x i j
        simp [lmulM]
      rw [hl1, Measure.map_id]
  have hOQ : IsOrbQuot (toBessel D τ w w' θ W lam' A hW hA hT hT') g (Measure.dirac one)
      (pairMeas (toBessel D τ w w' θ W lam' A hW hA hT hT')) := by
    intro F hF
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac]
    congr 1
    unfold stabAct
    rw [hof, Matrix.one_mul, Matrix.mul_one, hgi, Matrix.one_mul]
    rfl
  have hpt : (fun i j => (g⁻¹ * Matrix.of one * g) i j : Mt D.R.k D.R.rS) = one := by
    funext i j; rw [hof, Matrix.mul_one, hgi]
  have hmc : Measurable (fun x : Mt D.R.k D.R.rS => fun i j => (g⁻¹ * Matrix.of x * g) i j) := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j
  have hQM : IsQuotMeas W.μG ((Measure.dirac one).map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) W.μG := by
    have hmapd : (Measure.dirac one).map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j) = Measure.dirac one := by
      ext s hs
      rw [Measure.map_apply hmc hs, Measure.dirac_apply' _ (hmc hs), Measure.dirac_apply' _ hs]
      have hiff : one ∈ (fun x : Mt D.R.k D.R.rS => fun i j => (g⁻¹ * Matrix.of x * g) i j) ⁻¹' s ↔ one ∈ s := by
        rw [Set.mem_preimage]
        exact iff_of_eq (congrArg (· ∈ s) hpt)
      simp only [Set.indicator]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hiff.1 h1) h2
      · exact absurd (hiff.2 h2) h1
      · rfl
    rw [hmapd]
    intro F hF
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac]
    congr 1
    funext i j
    rw [hof, Matrix.one_mul]
    rfl
  have hMo : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS W.z W.z' g) := by
    rw [hgdef, Formalism.QuantumDeterminants.bigCellZhat _ _ _ _ _ _ hz hz']
    refine ⟨Equiv.refl _, fun a => if h : a.val < D.R.rS then q.1 ⟨a.val, h⟩ else
      herm (Hpk D.R.k D.R.rS) (Matrix.mulVec (bigCell D.R.k D.R.rS q.1 (μsec q.2)) W.z') W.z, fun a => ?_, ?_⟩
    · by_cases h : a.val < D.R.rS
      · simp only [dif_pos h]; exact hc _
      · simp only [dif_neg h]
        have hz0 := (Formalism.QuantumDeterminants.bigCellMinors _ _ _ _ q.1 (μsec q.2) hz hz').2.2 hc
        have hζ0 : q.2 ≠ 0 := by
          intro e; rw [e, Complex.normSq_zero] at hζ'
          have : 0 ≤ Tz D.R.k D.R.rS W.z * Tz D.R.k D.R.rS W.z' := by rw [hTz, hTz']; positivity
          linarith
        have h1 := Formalism.MainNotions.InterlacingSignCuts.bigCell_D D.R.k D.R.rS W.z W.z' hz hz' q.1 hc (μsec q.2)
        rw [(hsec.2 q.2 hζ').2] at h1
        rw [← hz0]
        unfold zeta
        rw [h1.2, mul_div_cancel_left₀ _ h1.1]
        exact hζ0
    · ext i j
      simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_apply, Matrix.of_apply, Equiv.refl_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
  have e1 := hfEq g hgU hGp hMo hRel (Measure.dirac one) W.μG (pairMeas (toBessel D τ w w' θ W lam' A hW hA hT hT'))
    hHaar hOQ hQM
  rw [e1]
  rfl

theorem ampUnif_of' (hAO : AmpOrbU) (hRC : RootCmp) (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of hAO big_cell_eq hRC hNZ

end Formalism.MainNotions.S.Pv.LemmaJ
