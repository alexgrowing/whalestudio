import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFlArith
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace PositivityTheory.Xgp.block_hermitian_pullback

namespace FlZero

section Block

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def omitV (q₀ : FlBlock Ψ N) : (Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1) → Σ q, FlIdx Ψ N q :=
  fun p => ⟨p.1.1, p.2⟩

theorem isBlockMap_omitV (q₀ : FlBlock Ψ N) :
    IsBlockMap (Subtype.val : {q : FlBlock Ψ N // q ≠ q₀} → FlBlock Ψ N) (omitV q₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨q, hq⟩, i⟩ ⟨⟨q', hq'⟩, i'⟩ h
    simp only [omitV, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl
  · rintro ⟨q, i⟩ ⟨y, rfl⟩
    exact ⟨⟨y, i⟩, rfl⟩

theorem isPullHerm_fs (q₀ : FlBlock Ψ N) (a : FlBlock Ψ N → ℤ) (ha : a q₀ = 0) :
    IsPullHerm (Subtype.val : {q : FlBlock Ψ N // q ≠ q₀} → FlBlock Ψ N) (omitV q₀)
      (fsHerm (fun q : {q : FlBlock Ψ N // q ≠ q₀} => FlIdx Ψ N q.1) fun k => a k.1)
      (fsHerm (FlIdx Ψ N) a) := by
  refine ⟨?_, ?_⟩
  · funext q
    show a q = Function.extend Subtype.val (fun k : {q : FlBlock Ψ N // q ≠ q₀} => a k.1) 0 q
    by_cases hq : q = q₀
    · subst hq
      rw [Function.extend_apply']
      · simpa using ha
      · rintro ⟨k, hk⟩
        exact k.2 hk
    · exact (Subtype.val_injective.extend_apply (fun k : {q : FlBlock Ψ N // q ≠ q₀} => a k.1) 0 ⟨q, hq⟩).symm
  · intro z
    simp only [fsHerm, refNorm]
    rw [← Finset.prod_erase _ (a := q₀)]
    · exact Finset.prod_subtype _ (by simp) _
    · simp [ha]

end Block

section Triv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp only at ha hh
  subst ha
  subst hh
  rfl

theorem fs_zero_tensor : (fsHerm ι (0 : K → ℤ)).tensor (fsHerm ι 0) = fsHerm ι 0 := by
  apply hermLine_ext
  · simp [HermLine.tensor, fsHerm]
  · funext z
    simp [HermLine.tensor, fsHerm, refNorm]

end Triv

end FlZero

open FlZero FlLines

private theorem imageZ_mCoordIdeal' {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type} {Ω : Type}
    [Field Ω] (κ : K → K') (v : (Σ k, ι k) → Σ k', ι' k') (hκ : Function.Injective κ)
    (hv : ∀ p, (v p).1 = κ p.1) (y : (Σ k', ι' k') → Ω) :
    imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v) := by
  ext g
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  have h : (mConeMap y) (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf =>
      simp only [map_mul, rename_X, hf]
      simp [mConeMap, hv]
  change (mConeMap y) (rename v g) = 0 ↔ (mConeMap (y ∘ v)) g = 0
  rw [h]
  constructor
  · intro h'
    exact rename_injective κ hκ (by rw [h', map_zero])
  · intro h'
    rw [h', map_zero]

private theorem II_fsHerm_yDeg_eq_zero_of_ne (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (hN : 2 ≤ N)
    (p : Ψ × Fin N) (hp : (p.2 : ℕ) + 1 < N)
    (w : Fin (antisymDegree Ψ N + 1) → Ψ × Fin N) (hw : ∀ j, w j ≠ p) :
    II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1)
      (fun r => fsHerm (FlIdx Ψ N) (yDeg Ψ N (w r))) = 0 := by
  have hdim : dimFl Ψ N = antisymDegree Ψ N := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  have hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]
    exact FlagArithVar.proof Ψ N hN
  have hq : (p.2 : ℕ) < N - 1 := by omega
  have hz : ∀ j, yDeg Ψ N (w j) (p.1, ⟨p.2, hq⟩) = 0 := by
    intro j
    unfold FlLines.yDeg
    split_ifs with h
    · exact absurd (Prod.ext h.1.symm (Fin.ext h.2.symm)) (hw j)
    · rfl
  generalize ((p.1, ⟨p.2, hq⟩) : FlBlock Ψ N) = q₀ at hz
  by_cases hK : Nonempty {q : FlBlock Ψ N // q ≠ q₀}
  · have hNe : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
    have hnz : ∀ k : FlBlock Ψ N, yFl Ψ N ⟨k, FlagArithVar.leadIdx Ψ N k⟩ ≠ 0 := by
      intro k h
      have h1 := PositivityTheory.Xgp.fl_arith.ev_lead k (0 : ℚ)
      have h2 : PositivityTheory.Xgp.fl_arith.yP ⟨k, FlagArithVar.leadIdx Ψ N k⟩ = 0 :=
        IsFractionRing.to_map_eq_zero_iff.mp h
      rw [h2, map_zero, map_zero] at h1
      exact zero_ne_one h1
    have hfinL : ∃ D : ℕ, Algebra.trdeg ℤ
        (Subfield.closure (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N))) = D := by
      have hs : (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N)).Finite := Set.finite_range _
      haveI : Algebra.EssFiniteType ℚ
          (IntermediateField.adjoin ℚ (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N))) :=
        IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hs)
      have hlt := _root_.trdeg_lt_aleph0 ℚ
        (IntermediateField.adjoin ℚ (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N)))
      rw [← FlagArithVar.trdeg_int_eq_rat, FlagArithVar.trdeg_int_adjoin] at hlt
      exact Cardinal.lt_aleph0.mp hlt
    obtain ⟨D, hD⟩ := hfinL
    have hA := PositivityTheory.Xgp.fl_arith.arith_of_trdeg hNe (yFl Ψ N) (FlagArithVar.leadIdx Ψ N) hnz D hD
    have hDn : D = antisymDegree Ψ N := by
      have h := hA.2.2.2.symm.trans hP.2.2.2
      have h' : D + 1 + Fintype.card (FlBlock Ψ N) =
          antisymDegree Ψ N + 1 + Fintype.card (FlBlock Ψ N) := by exact_mod_cast h
      omega
    have hle : Subfield.closure (coneRatios
          (fun p : (Σ k : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N k.1) => yFl Ψ N (omitV q₀ p))
          (fun k => FlagArithVar.leadIdx Ψ N k.1)) ≤
        Subfield.closure (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N)) := by
      apply Subfield.closure_mono
      rintro _ ⟨p, rfl⟩
      exact ⟨⟨p.1.1, p.2⟩, rfl⟩
    have hfix1 : ∀ (c : ℚ) (p : Σ k : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N k.1),
        PositivityTheory.Xgp.fl_arith.subF q₀ c (yFl Ψ N (omitV q₀ p)) = yFl Ψ N (omitV q₀ p) := by
      intro c p
      show PositivityTheory.Xgp.fl_arith.subF q₀ c (algebraMap _ (ΩFl Ψ N) (PositivityTheory.Xgp.fl_arith.yP ⟨p.1.1, p.2⟩)) =
        algebraMap _ (ΩFl Ψ N) (PositivityTheory.Xgp.fl_arith.yP ⟨p.1.1, p.2⟩)
      rw [PositivityTheory.Xgp.fl_arith.subF_alg, PositivityTheory.Xgp.fl_arith.sub_yP _ _ _ p.1.2]
    have hfix : ∀ (m : ℕ), ∀ x ∈ Subfield.closure (coneRatios
          (fun p : (Σ k : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N k.1) => yFl Ψ N (omitV q₀ p))
          (fun k => FlagArithVar.leadIdx Ψ N k.1)),
        PositivityTheory.Xgp.fl_arith.subF q₀ (m : ℚ) x = x := by
      intro m x hx
      have hsub : Subfield.closure (coneRatios
            (fun p : (Σ k : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N k.1) => yFl Ψ N (omitV q₀ p))
            (fun k => FlagArithVar.leadIdx Ψ N k.1)) ≤
          RingHom.eqLocusField (PositivityTheory.Xgp.fl_arith.subF q₀ (m : ℚ)) (RingHom.id _) := by
        rw [Subfield.closure_le]
        rintro _ ⟨p, rfl⟩
        show PositivityTheory.Xgp.fl_arith.subF q₀ (m : ℚ) (yFl Ψ N (omitV q₀ p) /
            yFl Ψ N (omitV q₀ ⟨p.1, FlagArithVar.leadIdx Ψ N p.1.1⟩)) =
          yFl Ψ N (omitV q₀ p) / yFl Ψ N (omitV q₀ ⟨p.1, FlagArithVar.leadIdx Ψ N p.1.1⟩)
        rw [map_div₀, hfix1, hfix1]
      exact hsub hx
    have ht : yFl Ψ N ⟨q₀, PositivityTheory.Xgp.fl_arith.nextIdx q₀⟩ / yFl Ψ N ⟨q₀, FlagArithVar.leadIdx Ψ N q₀⟩ ∈
        Subfield.closure (coneRatios (yFl Ψ N) (FlagArithVar.leadIdx Ψ N)) :=
      Subfield.subset_closure ⟨⟨q₀, PositivityTheory.Xgp.fl_arith.nextIdx q₀⟩, rfl⟩
    have hinj : Function.Injective fun m : ℕ => PositivityTheory.Xgp.fl_arith.subF q₀ (m : ℚ)
        (yFl Ψ N ⟨q₀, PositivityTheory.Xgp.fl_arith.nextIdx q₀⟩ / yFl Ψ N ⟨q₀, FlagArithVar.leadIdx Ψ N q₀⟩) := by
      have key : ∀ c : ℚ, PositivityTheory.Xgp.fl_arith.subF q₀ c
          (yFl Ψ N ⟨q₀, PositivityTheory.Xgp.fl_arith.nextIdx q₀⟩ / yFl Ψ N ⟨q₀, FlagArithVar.leadIdx Ψ N q₀⟩) =
          algebraMap _ (ΩFl Ψ N) (PositivityTheory.Xgp.fl_arith.sub q₀ c
            (PositivityTheory.Xgp.fl_arith.yP ⟨q₀, PositivityTheory.Xgp.fl_arith.nextIdx q₀⟩)) /
          algebraMap _ (ΩFl Ψ N) (PositivityTheory.Xgp.fl_arith.sub q₀ c
            (PositivityTheory.Xgp.fl_arith.yP ⟨q₀, FlagArithVar.leadIdx Ψ N q₀⟩)) := by
        intro c
        rw [map_div₀]
        exact congrArg₂ (· / ·) (PositivityTheory.Xgp.fl_arith.subF_alg q₀ c _) (PositivityTheory.Xgp.fl_arith.subF_alg q₀ c _)
      have hB : ∀ c : ℚ, algebraMap _ (ΩFl Ψ N) (PositivityTheory.Xgp.fl_arith.sub q₀ c
          (PositivityTheory.Xgp.fl_arith.yP ⟨q₀, FlagArithVar.leadIdx Ψ N q₀⟩)) ≠ 0 := by
        intro c h
        have h0 := PositivityTheory.Xgp.fl_arith.ev_lead q₀ c
        rw [IsFractionRing.to_map_eq_zero_iff.mp h, map_zero] at h0
        exact zero_ne_one h0
      intro a b hab
      simp only at hab
      rw [key, key, div_eq_div_iff (hB _) (hB _), ← map_mul, ← map_mul] at hab
      have h2 := congrArg PositivityTheory.Xgp.fl_arith.ev1 (IsFractionRing.injective _ (ΩFl Ψ N) hab)
      simp only [map_mul, PositivityTheory.Xgp.fl_arith.ev_next, PositivityTheory.Xgp.fl_arith.ev_lead, mul_one] at h2
      exact_mod_cast h2
    obtain ⟨d, hd, hdL⟩ := PositivityTheory.Xgp.fl_arith.trdeg_lt _ _ hle _ ht
      (fun m => PositivityTheory.Xgp.fl_arith.subF q₀ (m : ℚ)) hfix hinj D hD
    have hA' := PositivityTheory.Xgp.fl_arith.arith_of_trdeg hK
      (fun p : (Σ k : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N k.1) => yFl Ψ N (omitV q₀ p))
      (fun k => FlagArithVar.leadIdx Ψ N k.1) (fun k => hnz k.1) d hdL
    have himg : IsArithVar (imageZ (omitV q₀) (PFl Ψ N)) (d + 1) := by
      have hb := isBlockMap_omitV (Ψ := Ψ) (N := N) q₀
      rw [show PFl Ψ N = mCoordIdeal (yFl Ψ N) from rfl, imageZ_mCoordIdeal' _ _ hb.1 hb.2.2.1]
      exact hA'
    have hc := hII.2.2.2 {q : FlBlock Ψ N // q ≠ q₀} (fun q => FlIdx Ψ N q.1) (FlBlock Ψ N) (FlIdx Ψ N)
      Subtype.val (omitV q₀) (PFl Ψ N) (d + 1) (antisymDegree Ψ N + 1) 0
      (fun r => fsHerm (fun q : {q : FlBlock Ψ N // q ≠ q₀} => FlIdx Ψ N q.1) (fun k => yDeg Ψ N (w r) k.1))
      (fun r => fsHerm (FlIdx Ψ N) (yDeg Ψ N (w r))) Fin.elim0 (isBlockMap_omitV q₀) hP himg (by omega)
      (fun _ => FlagHeightMultilinear.isSmoothHerm_fsHerm _) (fun r => isPullHerm_fs q₀ _ (hz r))
      (fun j => j.elim0)
    rw [Fin.append_elim0] at hc
    exact hc
  · have hall : ∀ q : FlBlock Ψ N, q = q₀ := fun q => by_contra fun h => hK ⟨⟨q, h⟩⟩
    have hL : (fun r => fsHerm (FlIdx Ψ N) (yDeg Ψ N (w r))) = fun _ => fsHerm (FlIdx Ψ N) 0 := by
      funext r
      congr 1
      funext q
      rw [hall q]
      exact hz r
    rw [hL]
    have hu : Function.update (fun _ : Fin (antisymDegree Ψ N + 1) => fsHerm (FlIdx Ψ N) (0 : FlBlock Ψ N → ℤ)) 0
        (fsHerm (FlIdx Ψ N) 0) = fun _ => fsHerm (FlIdx Ψ N) 0 := by
      funext i
      simp [Function.update_apply]
    have hm := hII.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1)
      (fun _ => fsHerm (FlIdx Ψ N) 0) 0 (fsHerm (FlIdx Ψ N) 0) (fsHerm (FlIdx Ψ N) 0) hP
      (fun _ => FlagHeightMultilinear.isSmoothHerm_fsHerm _) (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
    rw [fs_zero_tensor, hu] at hm
    linarith

theorem flZero_main : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∀ (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N), (p.2 : ℕ) + 1 < N → gap lam p = 0 → eval lam (hFlPoly Ψ N II) = 0 := by
  intro _ II hII Ψ _ _ _ N hN lam p hp hgap
  have hdim : dimFl Ψ N = antisymDegree Ψ N := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  have hP : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]
    exact FlagArithVar.proof Ψ N hN
  have hfam := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  have hpoly : hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w =>
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1)
        fun r => fsHerm (FlIdx Ψ N) (yDeg Ψ N (w r))) := by
    apply FlLines.formPoly_eq_toWt
    intro μ
    have h1 := FlagHeightMultilinear.I_fsHerm_sum hfam hP (fun _ => μ) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hfam hP (fun _ => gapZ μ) (yDeg Ψ N)
    try simp only [] at h1 h2
    simp only [xLine]
    rw [← h1, ← h2, FlLines.deg_abel_smul]
  rw [hpoly, eval_toWt_gap]
  simp only [formPoly, map_sum, map_mul, map_prod, eval_C, eval_X]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : ∃ j, w j = p
  · obtain ⟨j, hj⟩ := hw
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; exact hgap)
  · push_neg at hw
    apply mul_eq_zero_of_left
    exact II_fsHerm_yDeg_eq_zero_of_ne II hII Ψ N hN p hp w hw

end PositivityTheory.Xgp.block_hermitian_pullback
