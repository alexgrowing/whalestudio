import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.KillOp
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RepOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AmpRep
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.BandRep
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPiecesK
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ExistsFinMap

noncomputable section

open MeasureTheory NumberField MvPolynomial Filter Topology UpperTheory.ConvolutionTheory PositivityTheory.Rg.Fx GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core

namespace UpperTheory.ConvolutionTheory.BW

open Op

section Abs

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem inv_ex (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (η : ℝ) (hη : 0 < η) (χ : ℝ → ℝ) (hχ : Continuous χ) (h0 : ∀ x ≤ η / 2, χ x = 0) :
    ∃ B : H →L[ℂ] H, A * B * fcalc χ A = fcalc χ A ∧ (∀ T, Commute T A → Commute T B ∧ Commute T (fcalc χ A)) := by
  have hs : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hg : Continuous fun x : ℝ => (max x (η / 2))⁻¹ :=
    (continuous_id.max continuous_const).inv₀ fun x => (lt_of_lt_of_le (half_pos hη) (le_max_right _ _)).ne'
  refine ⟨cfc (fun x : ℝ => (max x (η / 2))⁻¹) A, ?_, fun T hT => ⟨(hT.symm.cfc_real _).symm, (hT.symm.cfc_real _).symm⟩⟩
  have e : χ = fun x => x * (max x (η / 2))⁻¹ * χ x := by
    funext x
    rcases le_or_gt x (η / 2) with h | h
    · simp [h0 x h]
    · rw [max_eq_left h.le, mul_inv_cancel₀ ((half_pos hη).trans h).ne', one_mul]
  unfold fcalc
  conv_rhs => rw [e]
  rw [cfc_mul (fun x : ℝ => x * (max x (η / 2))⁻¹) χ A (continuous_id.mul hg).continuousOn hχ.continuousOn,
    cfc_mul (fun x : ℝ => x) (fun x : ℝ => (max x (η / 2))⁻¹) A continuous_id.continuousOn hg.continuousOn, cfc_id' ℝ A]

private theorem app_abs {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (UpperTheory.ConvolutionTheory.Pl K)) (ev : PR K n →+* (H →L[ℂ] H))
    (L : H →ₗ[ℂ] M) (z : MvPolynomial (Ix K n) ℂ →ₐ[ℂ] Module.End ℂ M) (h : UpperTheory.ConvolutionTheory.Pl K × Fin n → Module.End ℂ M)
    (hz : ∀ x v v', am ev v' = ev (C (X (some x))) v → L v' = z (X x) (L v))
    (h4 : ∀ p : UpperTheory.ConvolutionTheory.Pl K × Fin n, p.1 ∉ S → ∀ v, L (ev (X p) v) = h p (L v))
    (B : H →L[ℂ] H) (hB : ∀ R, Commute B (ev R))
    (W : H →L[ℂ] H) (hW : am ev * B * W = W) (g : MvPolynomial (UpperTheory.ConvolutionTheory.Pl K × Fin n) (MvPolynomial (Ix K n) ℂ))
    (hg : ∀ β ∈ g.support, ∀ p ∈ β.support, p.1 ∉ S) (u : H) :
    L (yk ev B W g u) = (∑ β ∈ g.support, z (g.coeff β) * (β.support.toList.map fun p => h p ^ β p).prod) (L (W u)) := by
  have h1 : ∀ (V : H →L[ℂ] H), am ev * B * V = V → ∀ x, L ((B * zm ev (Finsupp.single x 1) * V) u) = z (X x) (L (V u)) := by
    intro V hV x
    refine hz _ _ _ ?_
    have := fix_mul hB hV (T := zm ev (Finsupp.single x 1)) (ev_comm ev _ _) (hB _).symm
    rw [← zm_single, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, mul_assoc B, ← mul_assoc, this]
  have h2 : ∀ (α : Ix K n →₀ ℕ) (V : H →L[ℂ] H), am ev * B * V = V →
      L ((B ^ α.degree * zm ev α * V) u) = z (monomial α 1) (L (V u)) := by
    have fx : ∀ (α : Ix K n →₀ ℕ) (V : H →L[ℂ] H), am ev * B * V = V →
        am ev * B * (B ^ α.degree * zm ev α * V) = B ^ α.degree * zm ev α * V := fun α V hV =>
      fix_mul hB hV (((hB _).pow_left _).mul_left (ev_comm ev _ _)) (((Commute.refl B).pow_left _).mul_left (hB _).symm)
    have ad : ∀ a b : Ix K n →₀ ℕ, (∀ (V : H →L[ℂ] H), am ev * B * V = V →
        L ((B ^ a.degree * zm ev a * V) u) = z (monomial a 1) (L (V u))) → (∀ (V : H →L[ℂ] H), am ev * B * V = V →
        L ((B ^ b.degree * zm ev b * V) u) = z (monomial b 1) (L (V u))) → ∀ (V : H →L[ℂ] H), am ev * B * V = V →
        L ((B ^ (a + b).degree * zm ev (a + b) * V) u) = z (monomial (a + b) 1) (L (V u)) := by
      intro a b ha hb V hV
      have e : B ^ (a + b).degree * zm ev (a + b) * V = B ^ a.degree * zm ev a * (B ^ b.degree * zm ev b * V) := by
        have hc : Commute (B ^ b.degree) (zm ev a) := (hB _).pow_left _
        rw [map_add, pow_add, zm_add, mul_assoc (B ^ a.degree), ← mul_assoc (B ^ b.degree), hc.eq]
        simp only [mul_assoc]
      have e2 : (monomial (a + b) 1 : MvPolynomial (Ix K n) ℂ) = monomial a 1 * monomial b 1 := by rw [monomial_mul, one_mul]
      rw [e, ha _ (fx b V hV), hb V hV, e2, map_mul, Module.End.mul_apply]
    have z0 : ∀ (V : H →L[ℂ] H), am ev * B * V = V →
        L ((B ^ (0 : Ix K n →₀ ℕ).degree * zm ev 0 * V) u) = z (monomial 0 1) (L (V u)) := by
      intro V _
      simp [zm_zero]
    intro α
    induction α using Finsupp.induction_linear with
    | zero => exact z0
    | add a b ha hb => exact ad a b ha hb
    | single i e =>
      induction e with
      | zero => rw [Finsupp.single_zero]; exact z0
      | succ e ih =>
        rw [Finsupp.single_add]
        refine ad _ _ ih fun V hV => ?_
        rw [Finsupp.degree_single, pow_one]
        exact h1 V hV i
  have h3 : ∀ (p : MvPolynomial (Ix K n) ℂ) (V : H →L[ℂ] H), am ev * B * V = V →
      L ((tp ev B p * V) u) = z p (L (V u)) := by
    intro p V hV
    have e : z p = ∑ α ∈ p.support, p.coeff α • z (monomial α 1) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    rw [e, tp_eq, Finset.sum_mul, ContinuousLinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_mul_assoc, ContinuousLinearMap.smul_apply, map_smul, h2 α V hV, LinearMap.smul_apply]
  have h5 : ∀ p : UpperTheory.ConvolutionTheory.Pl K × Fin n, p.1 ∉ S → ∀ (e : ℕ) v, L (ev (X p ^ e) v) = (h p ^ e) (L v) := by
    intro p hp e
    induction e with
    | zero => simp
    | succ e ih => intro v; rw [pow_succ, pow_succ, map_mul, ContinuousLinearMap.mul_apply, ih, h4 p hp, Module.End.mul_apply]
  have h6 : ∀ (β : (UpperTheory.ConvolutionTheory.Pl K × Fin n) →₀ ℕ) (l : List (UpperTheory.ConvolutionTheory.Pl K × Fin n)), (∀ p ∈ l, p.1 ∉ S) → ∀ v,
      L (ev (l.map fun p => X p ^ β p).prod v) = (l.map fun p => h p ^ β p).prod (L v) := by
    intro β l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl v
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply,
        h5 p (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq), Module.End.mul_apply]
  rw [yk, ContinuousLinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [mul_assoc, h3 _ _ (fix_mul hB hW (ev_comm ev _ _) (hB _).symm), Module.End.mul_apply, ContinuousLinearMap.mul_apply,
    ← h6 β _ fun p hp => hg β hβ p (Finset.mem_toList.1 hp), Finset.prod_map_toList, monomial_eq, C_1, one_mul]
  rfl

private theorem core_abs {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (UpperTheory.ConvolutionTheory.Pl K)) (ev : PR K n →+* (H →L[ℂ] H))
    (A : H →L[ℂ] H) (hA : am ev = A) (hc : ∀ c : ℂ, ev (C (C c)) = c • 1) (hA0 : 0 ≤ A) (hA1 : ‖A‖ ≤ 1)
    (L : H →ₗ[ℂ] M) (z : MvPolynomial (Ix K n) ℂ →ₐ[ℂ] Module.End ℂ M) (h : UpperTheory.ConvolutionTheory.Pl K × Fin n → Module.End ℂ M)
    (hz : ∀ x v v', am ev v' = ev (C (X (some x))) v → L v' = z (X x) (L v))
    (h4 : ∀ p : UpperTheory.ConvolutionTheory.Pl K × Fin n, p.1 ∉ S → ∀ v, L (ev (X p) v) = h p (L v))
    (η : ℝ) (hη : 0 < η) (χ : ℝ → ℝ) (hχ : Continuous χ) (hχ0 : ∀ x ≤ η / 2, χ x = 0)
    (G : ℕ → MvPolynomial (UpperTheory.ConvolutionTheory.Pl K × Fin n) (MvPolynomial (Ix K n) ℂ))
    (s : Finset ((UpperTheory.ConvolutionTheory.Pl K × Fin n) →₀ ℕ)) (K₀ : ℝ) (hs : ∀ k, (G k).support ⊆ s) (hsS : ∀ β ∈ s, ∀ p ∈ β.support, p.1 ∉ S)
    (hG : ∀ k β, ((G k).coeff β).totalDegree ≤ k ∧ l1 ((G k).coeff β) ≤ K₀ ^ (k + 1) / k.factorial)
    (Pc P Q : H →L[ℂ] H) (hPc : ∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → Commute Pc (ev R))
    (hP : ∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → Commute P (ev R)) (hcQ : Pc ∘L Q = 0) (hPQ : P ∘L Q = 0)
    (hcusp : ∀ (u v y : H) (r : ℕ → H), A v = fcalc χ A u → P y = 0 → Tendsto (fun e => ‖r e‖) atTop (𝓝 0) →
      (∀ e, L (r e) = L y - ∑ k ∈ Finset.range e,
        (∑ β ∈ (G k).support, z ((G k).coeff β) * (β.support.toList.map fun p => h p ^ β p).prod) (L v)) → Pc (A y) = A y) :
    ∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ A ∘L Q‖ ≤ C ^ (d + 1) / d.factorial := by
  obtain ⟨B, hBX, hcm⟩ := inv_ex A hA0 η hη χ hχ hχ0
  set X₀ := fcalc χ A with hX₀
  have hB : ∀ R, Commute B (ev R) := fun R => (hcm _ (hA ▸ ev_comm ev R _)).1.symm
  have hW : am ev * B * X₀ = X₀ := hA ▸ hBX
  have hW' : am ev * B * (B * X₀) = B * X₀ := fix_mul hB hW (hB _) (Commute.refl B)
  have hoff : ∀ k, ∀ β ∈ (G k).support, ∀ p ∈ β.support, p.1 ∉ S := fun k β hβ => hsS β (hs k hβ)
  obtain ⟨c, x, hc0, hx, hyk⟩ := yk_norm ev B (B * X₀) G s K₀ hs hG
  obtain ⟨hsum, C', hC'⟩ := tail _ c x hc0 hx hyk ‖Q‖ (norm_nonneg _)
  set Y := ∑' k, yk ev B (B * X₀) (G k) with hY
  have hcY : ∀ T : H →L[ℂ] H, (∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → Commute T (ev R)) → Commute T A ∧ Commute T Y := by
    intro T hT
    have h1 : ∀ p, Commute T (ev (C p)) := fun p => hT _ (by simp)
    have h2 : Commute T A := hA ▸ h1 _
    refine ⟨h2, Commute.tsum_right _ fun k => comm_yk ev B (hcm T h2).1 ((hcm T h2).1.mul_right (hcm T h2).2) h1 fun β hβ => hT _ ?_⟩
    rw [vars_monomial one_ne_zero]
    exact hoff k β hβ
  have hzero : A * Y * Q = 0 := by
    ext1 u
    have hq1 : Pc (Q u) = 0 := congrArg (fun T : H →L[ℂ] H => T u) hcQ
    have hq2 : P (Q u) = 0 := congrArg (fun T : H →L[ℂ] H => T u) hPQ
    have c1 := hcY Pc hPc
    have c2 := hcY P hP
    have hp : Pc (A (Y (Q u))) = A (Y (Q u)) := by
      refine hcusp (Q u) ((B * X₀) (Q u)) _ (fun e => (Y - ∑ k ∈ Finset.range e, yk ev B (B * X₀) (G k)) (Q u)) ?_ ?_ ?_ fun e => ?_
      · rw [← ContinuousLinearMap.mul_apply, ← mul_assoc, hBX]
      · rw [← ContinuousLinearMap.mul_apply, c2.2.eq, ContinuousLinearMap.mul_apply, hq2, map_zero]
      · have t1 : Tendsto (fun e : ℕ => ‖(Y - ∑ k ∈ Finset.range e, yk ev B (B * X₀) (G k)) (Q u)‖) atTop (𝓝 (‖(Y - Y) (Q u)‖)) :=
          (((ContinuousLinearMap.apply ℂ H (Q u)).continuous.tendsto _).comp
            (tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat)).norm
        simpa only [sub_self, ContinuousLinearMap.zero_apply, norm_zero] using t1
      · rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sum_apply, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => app_abs S ev L z h hz h4 B hB _ hW' _ (hoff k) _
    show A (Y (Q u)) = 0
    rw [← hp, ← ContinuousLinearMap.mul_apply A, ← ContinuousLinearMap.mul_apply, (c1.1.mul_right c1.2).eq,
      ContinuousLinearMap.mul_apply, hq1, map_zero]
  refine ⟨C', fun d => le_trans ?_ (hC' d)⟩
  have e : ev (trunc d G) ∘L X₀ ∘L Q = A ^ (d + 1) * ((∑ k ∈ Finset.range (d + 1), yk ev B (B * X₀) (G k) - Y) * Q) := by
    show ev (trunc d G) * (X₀ * Q) = _
    rw [← mul_assoc, trunc_mul hc hB hW G (fun k β => (hG k β).1) d, hA, pow_succ, sub_mul, mul_sub,
      mul_assoc _ A (Y * Q), ← mul_assoc A Y, hzero]
    simp only [mul_assoc, mul_zero, sub_zero]
  rw [e]
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans (norm_mul_le _ _))
  exact (norm_pow_le' _ (Nat.succ_pos d)).trans (pow_le_one₀ (norm_nonneg _) hA1)

end Abs

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

private theorem pc_comm (hn : 0 < n) (𝔞 : Amp μ) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)) (hev : 𝔞.IsEv ev) (R : PR K n)
    (hR : ∀ y ∈ R.vars, y.1 ∉ 𝔞.S) : Commute (Pc μ) (ev R) := by
  obtain ⟨-, -, -, e0, he0, hi⟩ := UpperTheory.ConvolutionTheory.evEx K n hn μ 𝔞
  have hp : prj (cuspidalL2 μ) = Pc μ := by
    have hc : (cuspidalL2 μ).topologicalClosure = cuspidalL2 μ := (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
    unfold prj Pc
    congr 1
  have h0 : ∀ R, Commute (Pc μ) (e0 R) := fun R => by
    have := hi R _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
    rw [hp] at this
    exact Commute.symm this
  have hC : ∀ p, ev (C p) = e0 (C p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [hev.const, he0.const]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      rcases i with _ | x
      · rw [hev.amp, he0.amp]
      · rw [hev.cen, he0.cen]
  have : R ∈ supported (MvPolynomial (Option (Ix K n)) ℂ) {y : UpperTheory.ConvolutionTheory.Pl K × Fin n | y.1 ∉ 𝔞.S} := mem_supported.2 fun y hy => hR y hy
  rw [supported] at this
  clear hR
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨w, i⟩, hy, rfl⟩ := hx
    rw [hev.hecke w hy, ← he0.hecke w hy]
    exact h0 _
  | algebraMap r => rw [algebraMap_eq, hC]; exact h0 _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add_right hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy

theorem killCore (hn : 0 < n) (𝔞 : Amp μ) (η : ℝ) (hη : 0 < η) :
    ∃ (ρ : Typ K n) (Cb : ℝ), 0 ≤ Cb ∧ ∀ ev, 𝔞.IsEv ev → ∀ P Q : LL μ →L[ℂ] LL μ,
      (∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ 𝔞.S) → ev R ∘L P = P ∘L ev R) → Pc μ ∘L Q = 0 → P ∘L Q = 0 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x ≤ η / 2, χ x = 0) → ∀ F G, admitted 𝔞.S F → IsGen F G →
      (∀ (y : LL μ) (φ w : Sm K n), P y = 0 → Rep μ (𝔞.A y) w → Band Cb φ → Sph 𝔞.S φ → Killed ρ.ρ w.1 → Sph 𝔞.S w →
        IsSum G φ w → Cusp w.1) →
      ∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔞.A ∘L Q‖ ≤ C ^ (d + 1) / d.factorial := by
  classical
  obtain ⟨ρ, N, L, hL, hbd, hZ⟩ := ampRep K n μ 𝔞 hn
  obtain ⟨Cb, hCb, hband⟩ := bandRep K n μ 𝔞 η hn hη
  obtain ⟨hA0, hA1, -⟩ := UpperTheory.ConvolutionTheory.evEx K n hn μ 𝔞
  refine ⟨ρ, Cb, hCb, fun ev hev P Q hP hcQ hPQ χ hχ hχ0 F G hF hG hcusp => ?_⟩
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (UpperTheory.ConvolutionTheory.Pl K × Fin n) n F (by
    intro w
    convert hF.1 w)
  obtain rfl : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  have hA : am ev = 𝔞.A := hev.amp
  have uniq : ∀ v φ, Rep μ (𝔞.A v) φ → L v = φ := fun v φ h => (repOps K n μ hn _ _ (hL v).1).1 φ h
  refine core_abs 𝔞.S ev 𝔞.A hA hev.const hA0 hA1 L
    (((UpperTheory.V.Cm.uC K n).comp (Subalgebra.val _)).comp (evZ K n)) (fun p => hk n p.1 (p.2 + 1)) (fun x v v' h => ?_) ?_
    η hη χ hχ hχ0 G F.support K₀ (fun k => (hG₀ k).2.1)
    (fun β hβ p hp => hF.2 p ((mem_vars_iff_mem_support p).2 ⟨β, hβ, hp⟩)) (fun k => (hG₀ k).2.2) (Pc μ) P Q
    (pc_comm hn 𝔞 ev hev) (fun R hR => (hP R hR).symm) hcQ hPQ fun u v y r hv hy hr he => ?_
  · refine uniq _ _ ?_
    rw [hA, hev.cen] at h
    rw [h]
    exact hZ x _
  · rintro ⟨w, i⟩ hw v
    refine uniq _ _ ?_
    have e : 𝔞.A (ev (X (w, i)) v) = Tsph μ w i (𝔞.A v) := by
      rw [← hev.hecke w hw, ← hev.amp]
      exact congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (ev_comm ev _ _).eq
    rw [e]
    exact (repOps K n μ hn _ _ (hL v).1).2.2.2 w i ((hL v).2.2 w hw)
  · refine Submodule.starProjection_eq_self_iff.2 ((repOps K n μ hn _ _ (hL _).1).2.2.1 ?_)
    refine hcusp y (L v) _ hy (hL _).1 (hband χ hχ hχ0 u _ (hv ▸ (hL v).1)) (hL _).2.2 (hL _).2.1 (hL _).2.2 ⟨N, fun ε hε => ?_⟩
    obtain ⟨b, hb⟩ := hbd 1
    have t1 := hr.const_mul b
    rw [mul_zero] at t1
    filter_upwards [t1.eventually (ge_mem_nhds hε)] with e he' g
    have := hb (r e) g
    rw [map_one, Module.End.one_apply, he e] at this
    exact this.trans (mul_le_mul_of_nonneg_right he' (pow_nonneg (AutomorphicForm.height_pos g).le _))

end UpperTheory.ConvolutionTheory.BW
