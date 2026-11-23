import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLettersHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PhaseMove

theorem trace_sum_int : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → ∃ m : ℤ, 2 * (∑ τ, Formalism.MainNotions.TaylorLogMetric.embT D τ w).re = m := by
  intro D w hw
  have htr := Formalism.MainNotions.Ext.trace_sum_over_letters_holds D w
  have ht : IsIntegral ℤ (Algebra.trace D.host.K D.host.E w) := Algebra.isIntegral_trace hw
  obtain ⟨u, v, huv⟩ := ((GlobalTheory.MomDict.main D).2.2.1 _).2 ⟨⟨_, ht⟩, rfl⟩
  refine ⟨2 * u + v, ?_⟩
  rw [htr]
  erw [huv]
  simp [GlobalTheory.MomOne.wK]
  ring

def cTA (D : D7) {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin p) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  (B.map (Formalism.MainNotions.StandardLatticesGL3.sgA D)).transpose

theorem sq_unitary : ∀ {D : D7} {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∑ i, ∑ j, (((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j)) = ∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j) := by
  intro D a d x y A
  have hinv : ∀ e : D.host.E, D.host.conj (D.host.conj e) = e := fun e => by
    apply D.host.φ₀.injective
    have h1 := D.host.conjE_apply D.host.φ₀
    change D.host.φ₀ (D.host.conj (D.host.conj e)) = _
    rw [h1, h1, Complex.conj_conj]
  have hsg : ∀ u : Formalism.MainNotions.StandardLatticesGL3.AE D, Formalism.MainNotions.StandardLatticesGL3.sgA D (Formalism.MainNotions.StandardLatticesGL3.sgA D u) = u := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul e r =>
      change (Algebra.TensorProduct.map _ _) ((Algebra.TensorProduct.map _ _) (e ⊗ₜ r)) = e ⊗ₜ r
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact hinv e
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hΦ : ∀ B : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∑ i, ∑ j, B i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (B i j)) = (B * cTA D B).trace := fun B => by
    simp [cTA, Matrix.trace, Matrix.mul_apply]
  have hmul : ∀ {m p q : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (C : Matrix (Fin p) (Fin q) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (B * C) = cTA D C * cTA D B := fun B C => by
    simp only [cTA, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : ∀ {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (cTA D B) = B := fun B => by
    ext i j; simp [cTA, hsg]
  have hU : ∀ {m : ℕ} (g : Formalism.MainNotions.StandardLatticesGL3.GA D m), cTA D ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := fun g => by
    have h := g.2
    change Formalism.UG.cT _ _ * ((1 : Matrix _ _ D.host.E).map _) * _ = (1 : Matrix _ _ D.host.E).map _ at h
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    exact h
  set X : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hX
  set V : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hV
  set Y : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hY
  have hVX : V * X = 1 := by rw [hV, hX, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXc : X * cTA D X = 1 := mul_eq_one_comm.1 (hU x)
  have hVe : V = cTA D X := by
    calc V = V * (X * cTA D X) := by rw [hXc, Matrix.mul_one]
      _ = cTA D X := by rw [← Matrix.mul_assoc, hVX, Matrix.one_mul]
  have hVV : V * cTA D V = 1 := by rw [hVe, hcc, hU x]
  rw [hΦ, hΦ, hmul, hmul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hY1 : cTA D Y * Y = 1 := hU y
  rw [Matrix.mul_assoc (cTA D A), hY1, Matrix.mul_one, Matrix.trace_mul_comm]

theorem sq_move_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ A' : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∀ i j, ∃ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, A' i j - A i j = (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) → ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, (∑ i, ∑ j, A' i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A' i j)) - (∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j)) = (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  intro D cc a d A M hM
  obtain ⟨B, hB, hBA⟩ := GlobalTheory.NormSum.Expand.denom_fin (fun k : Fin d × Fin a => A k.1 k.2)
  obtain ⟨m, hm, hmI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D cc
  refine ⟨M * B * m, by positivity, fun A' hA' => ?_⟩
  choose t ht et using hA'
  have hsg : ∀ u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, Formalism.MainNotions.StandardLatticesGL3.sgA D u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun u hu =>
    GlobalTheory.NormSum.UnramHecke.sgA_mem D hu
  have hA1 : ∀ i j, (B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hBA (i, j)
  have ht1 : ∀ i j, (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hmI _ (ht i j)
  refine ⟨∑ i, ∑ j, (((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) +
      ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) +
      ((M * B * B : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j))),
    sum_mem fun i _ => sum_mem fun j _ => add_mem (add_mem (mul_mem (hA1 i j) (hsg _ (ht1 i j)))
      (mul_mem (ht1 i j) (hsg _ (hA1 i j)))) (mul_mem (natCast_mem _ _) (mul_mem (ht1 i j) (hsg _ (ht1 i j)))), ?_⟩
  have hA' : ∀ i j, A' i j = A i j + ((M * B * m : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j := fun i j => by
    rw [← et i j]; ring
  simp only [hA', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_mul, map_natCast]
  push_cast
  ring

theorem sq_diff_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ z' : Matrix (Fin d) (Fin a) D.host.E, Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' → IsIntegral ℤ (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) := by
  intro D cc a d x y z M hM
  obtain ⟨n, hn, h⟩ := sq_move_int cc ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)))) M hM
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨s, hs, e⟩ := h (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) fun i j => by
    obtain ⟨t, ht, et⟩ := hz' i j
    exact ⟨t, ht, by rw [← et, Matrix.sub_apply]⟩
  rw [sq_unitary] at e
  have hinc : ∀ w : Matrix (Fin d) (Fin a) D.host.E, (∑ i, ∑ j, w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j)) = Formalism.MainNotions.StandardLatticesGL3.inc D (∑ i, ∑ j, w i j * D.host.conj (w i j)) := fun w => by
    simp only [Matrix.map_apply, map_sum, map_mul]
    rfl
  rw [hinc, hinc, ← map_sub] at e
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← GlobalTheory.HeckeVal.inc_mem_iff]
  have e2 : Formalism.MainNotions.StandardLatticesGL3.inc D (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) = Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    rw [div_eq_inv_mul, map_mul, e, mul_assoc]
  have e3 : Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
    rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hM0, map_one]
  rw [e2, e3, one_mul]
  exact hs

theorem qH_pt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.qH D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) =
      (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))).re / (Ideal.absNorm cc : ℝ) := by
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hC
  have hN : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  have hd : (0 : ℝ) < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hc : ∀ τ x, embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) := fun τ x =>
    D.host.conjE_apply (embT D τ) x
  have hpt : ∀ τ i j, pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := fun τ i j => rfl
  have hS : ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j)) =
      ∑ τ, ∑ i, ∑ j, embT D τ (z i j) * starRingEnd ℂ (embT D τ (z i j)) := by
    simp only [map_sum, map_mul, hc]
  have hH : Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ z) =
      ((Complex.normSq δ : ℝ) : ℂ) * (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))) /
        ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [hS, Hf]
    simp only [hpt, map_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [Formalism.MainNotions.TaylorLogMetric.qH, hH, GlobalTheory.MomDict.area_lamOf D cc δ hC.1.1]
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  rw [show ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) =
    ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) from rfl,
    mul_div_assoc, Complex.re_ofReal_mul, Complex.div_ofReal_re]
  field_simp

theorem phase_eq : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D cc δ hC a d x y z
  have hN : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  obtain ⟨n, hn, h⟩ := sq_diff_int cc x y z (8 * Ideal.absNorm cc) (by positivity)
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨m, hm⟩ := trace_sum_int D _ (h z' hz')
  set S' := ∑ i, ∑ j, z' i j * D.host.conj (z' i j)
  set S := ∑ i, ∑ j, z i j * D.host.conj (z i j)
  have h8 : ((8 * Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hsplit : S' = S + ((8 * Ideal.absNorm cc : ℕ) : D.host.E) * ((S' - S) / ((8 * Ideal.absNorm cc : ℕ) : D.host.E)) := by
    field_simp; ring
  have key : (∑ τ, embT D τ S').re = (∑ τ, embT D τ S).re + 4 * (Ideal.absNorm cc : ℝ) * m := by
    rw [hsplit]
    simp only [map_add, map_mul, map_natCast, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re]
    have e : ((8 * Ideal.absNorm cc : ℕ) : ℂ) = (((8 * Ideal.absNorm cc : ℕ) : ℝ) : ℂ) := rfl
    rw [e, Complex.re_ofReal_mul]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hN' : (0 : ℝ) < Ideal.absNorm cc := by exact_mod_cast hN
  have harg : (∑ τ, embT D τ S').re / (Ideal.absNorm cc : ℝ) / 2 =
      (∑ τ, embT D τ S).re / (Ideal.absNorm cc : ℝ) / 2 + 2 * m := by
    rw [key]; field_simp; ring
  rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.StandardLatticesGL3.wdPh, qH_pt hC z', qH_pt hC z, harg]
  unfold Formalism.MainNotions.StandardLatticesGL3.ee
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2 * m, ?_⟩
  push_cast
  ring

end GlobalTheory.PhaseMove
