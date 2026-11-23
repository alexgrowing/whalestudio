import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXyStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPointStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Transfer
variable {q : ℕ} [Fact q.Prime]

def Tr (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (p : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ (fun z => F (z + p)) 0 ∧ Bdd (hat ι ℓ F) ∧
    hat ι ℓ (fun z => F (z + p)) = shiftS ζ (hat ι ℓ F)

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).1⟩

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).2⟩

section
variable {ι : ℂ ≃+* ℂ_[q]} {ℓ : ℂ_[q]⟦X⟧} {ζ : ℂ_[q]} {p : ℂ}

lemma Tr.const (h0 : constantCoeff ℓ = 0) (c : ℂ) : Tr ι ℓ ζ p (fun _ => c) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).2.1 c
  refine ⟨analyticAt_const, analyticAt_const, ⟨‖ι c‖, fun n => ?_⟩, ?_⟩
  · rw [h, coeff_C]
    split_ifs <;> simp
  · rw [h, Shift.shiftS_C]

lemma Tr.add (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z + G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.add g1, f2.add g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).1]; exact bdd_add f3 g3
  · rw [(h _ _ f1 g1).1, (h _ _ f2 g2).1, f4, g4, Shift.shiftS_add hζ f3 g3]

lemma Tr.mul (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z * G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.mul g1, f2.mul g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).2.1]; exact bdd_mul f3 g3
  · rw [(h _ _ f1 g1).2.1, (h _ _ f2 g2).2.1, f4, g4, Shift.shiftS_mul hζ f3 g3]

lemma Tr.pow (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F : ℂ → ℂ} (hF : Tr ι ℓ ζ p F) (n : ℕ) :
    Tr ι ℓ ζ p (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 1
  | succ n ih => simpa only [pow_succ] using Tr.mul h0 hζ ih hF

lemma Tr.sum (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) (F : ℕ → ℂ → ℂ) (hF : ∀ i, Tr ι ℓ ζ p (F i))
    (n : ℕ) : Tr ι ℓ ζ p (fun z => ∑ i ∈ Finset.range n, F i z) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 0
  | succ n ih => simpa only [Finset.sum_range_succ] using Tr.add h0 hζ ih (hF n)

lemma exists_homog (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {u w : ℂ → ℂ} (hu : Tr ι ℓ ζ p u)
    (hw : Tr ι ℓ ζ p w) (A : Polynomial ℂ) :
    ∃ (k : ℕ) (F : ℂ → ℂ), Tr ι ℓ ζ p F ∧ ∀ z x : ℂ, x * w z = u z → F z = A.eval x * w z ^ k := by
  refine ⟨A.natDegree, fun z => ∑ i ∈ Finset.range (A.natDegree + 1),
    A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)), ?_, fun z x hx => ?_⟩
  · exact Tr.sum h0 hζ (fun i z => A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)))
      (fun i => Tr.mul h0 hζ (Tr.const h0 _) (Tr.mul h0 hζ (hu.pow h0 hζ i) (hw.pow h0 hζ _))) _
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi'
    rw [← hx, hj, Nat.add_sub_cancel_left]
    ring

lemma exists_quot (h0 : constantCoeff ℓ = 0) (h1 : coeff 1 ℓ ≠ 0) {f D N : ℂ → ℂ} (S : ℂ_[q]⟦X⟧)
    (hf : MeromorphicAt f 0) (hD : AnalyticAt ℂ D 0) (hN : AnalyticAt ℂ N 0)
    (hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0) (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z * D z = N z)
    (hS : S * hat ι ℓ D = hat ι ℓ N) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
  obtain ⟨h, hc, hid, hcc, -⟩ := TaylorRead.hat_laws q ι ℓ h0
  have hDne : hat ι ℓ D ≠ 0 := by
    intro hz
    have e : hat ι ℓ D = hat ι ℓ (fun _ => 0) := by rw [hz, hc]; simp
    have e2 := (h _ _ hD analyticAt_const).2.2.2 h1 e
    obtain ⟨z, hz1, hz2⟩ := (hD0.and (e2.filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  have hpow : ∀ n : ℕ, hat ι ℓ (fun z => z ^ n) = ℓ ^ n := by
    intro n
    induction n with
    | zero => simpa using hc 1
    | succ n ih =>
      simp only [pow_succ]
      rw [(h (fun z => z ^ n) (fun z => z) (by fun_prop) (by fun_prop)).2.1, ih, hid]
  have key : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      hat ι ℓ g = ℓ ^ n * S := by
    intro n g hg hge
    apply mul_right_cancel₀ hDne
    rw [mul_assoc, hS, ← hpow, ← (h _ _ hg hD).2.1, ← (h (fun z => z ^ n) N (by fun_prop) hN).2.1]
    refine (h _ _ (hg.mul hD) (AnalyticAt.mul (by fun_prop) hN)).2.2.1 ?_
    filter_upwards [hge, he] with z a b
    show g z * D z = z ^ n * N z
    rw [a, ← b, mul_assoc]
  have main : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
    intro n
    induction n with
    | zero =>
      intro g hg hge
      exact ⟨g, hg, by simpa using hge, by simpa using key 0 g hg hge⟩
    | succ n ih =>
      intro g hg hge
      have hg0 : g 0 = 0 := by
        have := congrArg constantCoeff (key _ g hg hge)
        rw [hcc] at this
        simpa [h0] using this
      obtain ⟨s, hs⟩ := hg
      refine ih (dslope g 0) ⟨_, hs.has_fpower_series_dslope_fslope⟩ ?_
      filter_upwards [hge, self_mem_nhdsWithin] with z a hz
      have hz' : z ≠ 0 := hz
      rw [dslope_of_ne _ hz', slope_def_field, hg0, a]
      field_simp
      ring
  obtain ⟨n, hn⟩ := hf
  exact main n _ hn (Filter.Eventually.of_forall fun z => by simp)
end

lemma x_ne (M : Mdl q) (hM : M.Ok) (c z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, M.x z - c ≠ 0 := by
  obtain ⟨-, -, hx, -, u0, w0, du, -, hs⟩ := uw_elliptic_flow q M hM
  have hm : Meromorphic (fun z => M.x z - c) := fun z => (hx.1 z).sub (MeromorphicAt.const c z)
  have h0 : meromorphicOrderAt (fun z => M.x z - c) 0 ≠ ⊤ := by
    intro ht
    rw [meromorphicOrderAt_eq_top_iff] at ht
    obtain ⟨au, aw, -, -, e1, e2⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
    have dw : deriv M.w 0 = 0 := by
      have := e2.self_of_nhds.2.2
      simpa [u0, w0] using this
    have e3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u z = c * M.w z := by
      filter_upwards [ht, e1] with z a b
      rw [← b.2.2.1, sub_eq_zero.mp a]
    have e4 : M.u =ᶠ[𝓝 0] fun z => c * M.w z := by
      rw [eventually_nhdsWithin_iff] at e3
      filter_upwards [e3] with z a
      by_cases hz : z = 0
      · simp [hz, u0, w0]
      · exact a hz
    have := e4.deriv_eq
    rw [du, deriv_const_mul _ aw.differentiableAt, dw, mul_zero] at this
    exact hM.1 this
  have h1 := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩ z₀
  rcases (hm z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h) h1
  · exact h

lemma tendsto_add_punct (p : ℂ) : Filter.Tendsto (fun z : ℂ => z + p) (𝓝[≠] 0) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 (0 + p)) :=
      (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem shift_eq_hat_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  intro q _ M ω ζ p φ hch hat' hφ hφ0 hφb
  have hM : M.Ok := hch.1
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hζ : ‖ζ - 1‖ < 1 := hat'.2.1
  obtain ⟨h1, v, xs, ys, -, -, bys, -, -, cys, -, hwy, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hch
  obtain ⟨tu, tw⟩ := GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hch hat'
  obtain ⟨m, P, A, B, -, hAB⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hM hφ
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := uw_elliptic_flow q M hM
  obtain ⟨au0, aw0, -, -, e0, -⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨aup, awp, -, -, ep, -⟩ := hs p hat'.1
  have htr : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu : Tr M.ι (C ω * logS) ζ p M.u :=
    ⟨au0, aup.comp_of_eq htr (zero_add p), ⟨1, hch.2.2.1⟩, tu⟩
  have hw : Tr M.ι (C ω * logS) ζ p M.w := by
    refine ⟨aw0, awp.comp_of_eq htr (zero_add p), ⟨1, ?_⟩, tw⟩
    refine (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 bys cys ?_
    rw [pow_zero, one_mul, mul_comm, hwy]
    intro n
    rw [map_neg, norm_neg, coeff_X_pow]
    split_ifs <;> simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hQ
  obtain ⟨a, FQ, tQ, eQ⟩ := exists_homog h0 hζ hu hw Q
  obtain ⟨b, FA, tA, eA⟩ := exists_homog h0 hζ hu hw A
  obtain ⟨c, FB, tB, eB⟩ := exists_homog h0 hζ hu hw B
  have tD : Tr M.ι (C ω * logS) ζ p (fun z => FQ z * M.w z ^ (b + c + 1)) :=
    tQ.mul h0 hζ (hw.pow h0 hζ _)
  have tN : Tr M.ι (C ω * logS) ζ p
      (fun z => M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b))) :=
    (hw.pow h0 hζ _).mul h0 hζ ((tA.mul h0 hζ (hw.pow h0 hζ _)).add h0 hζ
      ((Tr.const h0 (-1)).mul h0 hζ (tB.mul h0 hζ (hw.pow h0 hζ _))))
  have hid : ∀ z, (z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) →
      φ z * Q.eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z →
      φ z * (FQ z * M.w z ^ (b + c + 1)) =
        M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b)) := by
    intro z e1 e2
    rw [eQ z _ e1.2.2.1, eA z _ e1.2.2.1, eB z _ e1.2.2.1, ← e1.2.2.2]
    linear_combination M.w z ^ (a + b + c + 1) * e2
  have h := (TaylorRead.hat_laws q M.ι _ h0).1
  refine exists_quot h0 h1 _ ?_ tD.2.1 tN.2.1 ?_ ?_ ?_
  · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + p) (hφ.1 _) htr
  · have hQ0 : ∀ᶠ z in 𝓝[≠] p, ∀ i, M.x z - M.x (P i) ≠ 0 :=
      Filter.eventually_all.2 fun i => x_ne M hM _ p
    refine (tendsto_add_punct p).eventually (p := fun z => FQ z * M.w z ^ (b + c + 1) ≠ 0) ?_
    filter_upwards [hQ0, ep] with z a1 a2
    have hw0 : M.w z ≠ 0 := by
      intro hz
      have := a2.2.2.2
      rw [hz] at this
      simp at this
    rw [eQ z _ a2.2.2.1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hw0)) (pow_ne_zero _ hw0)
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using a1 i
  · exact (tendsto_add_punct p).eventually ((ep.and (hAB p)).mono fun z hz => hid z hz.1 hz.2)
  · rw [tD.2.2.2, tN.2.2.2, ← Shift.shiftS_mul hζ hφb tD.2.2.1, ← (h _ _ hφ0 tD.1).2.1]
    congr 1
    exact (h _ _ (hφ0.mul tD.1) tN.1).2.2.1 ((e0.and (hAB 0)).mono fun z hz => hid z hz.1 hz.2)

end GlobalTheory.MomOne.Transfer
