import Formalism.GaussJetBounds.StatementU
import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.GaussJetBounds.MonoShapeTop
import Formalism.GaussJetBounds.GaussJetProofs.GField
import Formalism.GaussJetBounds.GaussJetProofs.Transfer
import Formalism.GaussJetBounds.GaussJetProofs.FJEval
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.GaussJetProofs.Labels
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

namespace OneGauss

def expo {K : Type} [Field K] {τ ι : Type} [Fintype τ] (v : τ → MvPowerSeries ι K) (sgn ep : K)
    (be : MvPowerSeries (ZMod 2) K) : MvPowerSeries ι K :=
  (sgn / 2) • ∑ x : τ, MvPowerSeries.subst
    (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) • v x) be

section Expo

variable {K : Type} [Field K] {τ ι : Type} [Fintype τ]

lemma cc_smul (c : K) {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (c • f) = 0 := by
  simp [MvPowerSeries.smul_eq_C_mul, hf]

lemma cc_expo (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (expo v sgn ep be) = 0 := by
  unfold expo
  refine cc_smul _ ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => cc_smul _ (hv x))
    (fun s => cc_smul _ (hv x)) hbe

lemma subst_expo {ι' : Type} {a : ι → MvPowerSeries ι' K} (hs : MvPowerSeries.HasSubst a)
    (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    MvPowerSeries.subst a (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.subst a (v x)) sgn ep be := by
  unfold expo
  rw [MvPowerSeries.subst_smul hs, ← MvPowerSeries.substAlgHom_apply hs, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ s : ZMod 2,
      MvPowerSeries.constantCoeff ((if s = 0 then (1 : K) else ep) • v x) = 0 :=
    fun s => cc_smul _ (hv x)
  rw [MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero h) hs]
  congr 1
  funext s
  rw [MvPowerSeries.subst_smul hs]

lemma map_expo {F : Type} [Field F] (φ : F →+* K) (v : τ → MvPowerSeries ι F)
    (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0) (sgn ep : F)
    (be : MvPowerSeries (ZMod 2) F) :
    MvPowerSeries.map φ (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.map φ (v x)) (φ sgn) (φ ep) (MvPowerSeries.map φ be) := by
  unfold expo
  have hs : ∀ (c : F) (f : MvPowerSeries ι F),
      MvPowerSeries.map φ (c • f) = φ c • MvPowerSeries.map φ f := by
    intro c f
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.smul_eq_C_mul]
  rw [hs, map_sum, map_div₀, map_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ s : ZMod 2,
      MvPowerSeries.constantCoeff ((if s = 0 then (1 : F) else ep) • v x) = 0 :=
    fun s => by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, hv x, mul_zero]
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h)]
  congr 1
  funext s
  rw [hs]
  split_ifs <;> simp

end Expo

lemma map_oneLog {F K : Type} [Field F] [Field K] (φ : F →+* K) {τ : Type} [DecidableEq τ]
    (l : ℕ) (x : τ) : MvPowerSeries.map φ (oneLog (K := F) l x) = oneLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (oneLog (K := F) l x n) = oneLog (K := K) l x n
  simp [oneLog, map_sum, apply_ite]

section Theta

variable {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}

lemma thetaOne_eq (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    thetaOne g U sgn ep be = MvPowerSeries.subst g U *
      mvExp (expo (fun x => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) sgn ep be) :=
  rfl

lemma map_thetaOne {F : Type} [NormedField F] [CharZero F] (φ : F →+* K)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaOne g U sgn ep be) =
      thetaOne (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ sgn) (φ ep)
        (MvPowerSeries.map φ be) := by
  rw [thetaOne_eq, thetaOne_eq, map_mul,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg),
    Transfer.map_mvExp φ (cc_expo _ (fun x => MvPowerSeries.constantCoeff_X x) _ _ _ hbe),
    map_expo φ _ (fun x => MvPowerSeries.constantCoeff_X x)]
  simp only [MvPowerSeries.map_X]

lemma subst_thetaOne {ι : Type} {a : Fin N0 × Fin N1 → MvPowerSeries ι K}
    (hs : MvPowerSeries.HasSubst a)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.subst a (thetaOne g U sgn ep be) =
      MvPowerSeries.subst a (MvPowerSeries.subst g U) * mvExp (expo a sgn ep be) := by
  rw [thetaOne_eq, MvPowerSeries.subst_mul hs,
    subst_mvExp hs _ (cc_expo _ (fun x => MvPowerSeries.constantCoeff_X x) _ _ _ hbe),
    subst_expo hs _ (fun x => MvPowerSeries.constantCoeff_X x)]
  simp only [MvPowerSeries.subst_X hs]

end Theta

def frA {K : Type} [Field K] {N0 N1 : ℕ} (Y : Fin N0 × Fin N0 → K) :
    Fin N0 × Fin N1 → Fin N0 × Fin N1 → K :=
  fun y z => if y.2 = z.2 then Y (y.1, z.1) else 0

lemma sum_frA_row {K : Type} [Field K] {N0 N1 : ℕ} (Y : Fin N0 × Fin N0 → K) (i : Fin N0)
    (b : Fin N1) :
    (∑ j : Fin N0 × Fin N1, MvPolynomial.C (frA Y (i, b) j) * MvPolynomial.X j :
      MvPolynomial (Fin N0 × Fin N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (Y (i, a)) * MvPolynomial.X (a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
  · simp [frA]
  · intro c _ hc
    simp [frA, Ne.symm hc]
  · simp

lemma eval₂_frameJetOne {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K]
    (φ : F →+* K) {N0 N1 C : ℕ} (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
    (Y : Fin N0 × Fin N0 → K) :
    MvPolynomial.eval₂ φ Y (frameJetOne p hp I (thetaOne g U sgn ep be)) =
      jetPair (minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)
        (MvPowerSeries.subst
            (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K))
            (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
          mvExp (expo (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K)) (φ sgn) (φ ep) (MvPowerSeries.map φ be))) := by
  have hlin : MvPowerSeries.HasSubst (fun x : Fin N0 × Fin N1 =>
      (∑ i : Fin N0 × Fin N1, MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
        MvPowerSeries (Fin N0 × Fin N1) K)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro x
    simp
  have hbe' : MvPowerSeries.constantCoeff (MvPowerSeries.map φ be) = 0 := by
    simp [hbe]
  rw [← subst_thetaOne hlin _ _ _ _ _ hbe', ← map_thetaOne φ g hg U sgn ep be hbe,
    jet_pair_linearity K (Fin N0 × Fin N1) (Fin N0 × Fin N1) (frA Y)]
  unfold frameJetOne
  rw [eval₂_jetPairPoly, ringMap_minorProd, map_minorProd]
  congr 2
  funext i b
  rw [MvPolynomial.aeval_X, sum_frA_row]
  simp

lemma degree_plain {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (κ : Fin N0 × Fin N1 →₀ ℕ)
    (hκ : κ ∈ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I).support) :
    κ.degree = ∑ c, p c := by
  have hdet : ∀ c : Fin C, (Matrix.of fun (r r' : Fin (p c)) =>
      (MvPolynomial.X (⟨(r : ℕ), lt_of_lt_of_le r.2 (hp c)⟩, I c r') :
        MvPolynomial (Fin N0 × Fin N1) K)).det.IsHomogeneous (p c) := by
    intro c
    rw [Matrix.det_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro s _
    have hprod := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin (p c)))
      (fun i => (Matrix.of fun (r r' : Fin (p c)) =>
        (MvPolynomial.X (⟨(r : ℕ), lt_of_lt_of_le r.2 (hp c)⟩, I c r') :
          MvPolynomial (Fin N0 × Fin N1) K)) (s i) i) (fun _ => 1)
      (fun i _ => by simpa using MvPolynomial.isHomogeneous_X K _)
    have hsum : (∑ _i ∈ (Finset.univ : Finset (Fin (p c))), 1) = p c := by simp
    rw [hsum] at hprod
    rw [Units.smul_def, zsmul_eq_mul,
      ← map_intCast (MvPolynomial.C : K →+* MvPolynomial (Fin N0 × Fin N1) K)]
    exact hprod.C_mul _
  have hmin := MvPolynomial.IsHomogeneous.prod Finset.univ _ _ (fun c _ => hdet c)
  have h := hmin (MvPolynomial.mem_support_iff.mp hκ)
  rw [Finsupp.degree_eq_weight_one]
  exact h

end OneGauss

open OneGauss in
theorem one_letter_gauss_sum : OneLetterGauss := by
  intro l _ N0 N1 C hl3 K0 hK0 ζ hζ be hbe ep hep g hg hgl U hU sgn hsgn p hp I a ha hpa n
  have hprime : Nat.Prime l := Fact.out
  haveI : Fact (1 < l) := ⟨hprime.one_lt⟩
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    push_cast at h
    rw [h]
    exact Padic.norm_p_lt_one
  obtain ⟨K, _, _, _, φ, Y, hφ, hY, hgen⟩ := residuallyGenericExists l (Fin N0 × Fin N0)
  have hlK : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hYn : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgen (MvPolynomial.X y) (by simp [MvPolynomial.X_ne_zero])
    rw [MvPolynomial.aeval_X] at h
    exact h.le
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := Transfer.cc_of_noLow hbe.2.2.1
  have hG := gauss_sum_powers ℂ_[l] K φ (Fin N0 × Fin N0) Y hY (fun _ => 1) (fun _ => one_ne_zero)
    (frameJetOne p hp I (thetaOne g U sgn ep be)) n
  simp only [pow_one] at hG
  refine hG.trans ?_
  rw [eval₂_frameJetOne φ g hg U sgn ep be hbe0 p hp I Y]
  have TB := admissibleTransfer ℂ_[l] K φ hφ l 2 0 0 K0 ζ be
  have hg' : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g x)) = 0 := by
    intro x
    simp [hg x]
  have hgl' : ∀ x : Fin N0 × Fin N1, MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (oneLog (K := K) l x) =
      MvPowerSeries.X x := by
    intro x
    have h := congrArg (MvPowerSeries.map φ) (hgl x)
    rwa [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_oneLog,
      MvPowerSeries.map_X] at h
  have hsgn' : φ sgn = 1 ∨ φ sgn = -1 := by
    rcases hsgn with h | h
    · left
      simp [h]
    · right
      simp [h]
  have hfrA : ∀ (x : Fin N0 × Fin N1) (i : Fin N0 × Fin N1), ‖frA Y i x‖ ≤ 1 := by
    intro x i
    unfold frA
    split_ifs
    · exact hYn _
    · simp
  have hmin : ∀ κ, ‖MvPolynomial.coeff κ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)‖ ≤ 1 := by
    have hm := minorProd_mem_opInt (K := K) (σ := Fin N0 × Fin N1)
      (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K))
      (fun i b κ => by
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp) p hp I
    exact hm
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hprime.ne_zero
  unfold jetPair
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro κ hκ
  have hR := oneLetterR K l N0 N1 hprime (hprime.odd_of_ne_two (by omega)) (hlK ▸ hl1)
    (Subfield.map φ K0) (TB.1 hK0) (φ ζ) (hζ.map_of_injective φ.injective)
    (MvPowerSeries.map φ be) (TB.2.1 hbe) (φ ep) (by rw [hφ, hep]) (Fin N0 × Fin N1)
    (fun x i => frA Y i x) (fun x i => hfrA x i) (fun y => MvPowerSeries.map φ (g y)) hg' hgl'
    (MvPowerSeries.map φ U) (Transfer.integral_map φ hφ hU) (φ sgn) hsgn' κ
  rw [degree_plain p hp I κ hκ, hlK] at hR
  rw [mul_assoc, norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hmin κ)) (le_trans hR ?_)
  apply Real.rpow_le_rpow_of_exponent_ge hlpos hl1.le
  have hcard : ((Fintype.card (Fin N0 × Fin N1) : ℕ) : ℝ) = (N0 : ℝ) * N1 := by simp
  rw [hcard]
  have hlog : Real.logb l (∑ c, p c : ℕ) ≤ Real.logb l a := by
    rcases Nat.eq_zero_or_pos (∑ c, p c) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by exact_mod_cast hprime.one_lt) (by exact_mod_cast ha)
    · exact Real.logb_le_logb_of_le (by exact_mod_cast hprime.one_lt) (by exact_mod_cast hpos)
        (by exact_mod_cast hpa)
  have hN : (0 : ℝ) ≤ (N0 : ℝ) * N1 := by positivity
  nlinarith

end Formalism.DworkPowerSeriesWeights
