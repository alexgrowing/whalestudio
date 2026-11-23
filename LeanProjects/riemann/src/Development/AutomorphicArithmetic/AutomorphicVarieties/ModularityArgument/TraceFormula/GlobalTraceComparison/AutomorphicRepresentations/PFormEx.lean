import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

private theorem weight_ex : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
    (∀ s ∈ Set.Ioo (-1 : ℝ) 1, w s ≠ 0) ∧ ∫ s, w s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.nonneg_normed, ?_,
    b.integral_normed⟩
  intro s hs
  have h : s ∈ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.2 hs
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def slabSp (D : Dom E n 0) : Submodule ℂ (GA E n → ℂ) where
  carrier := {f | Slab D f}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl, fun u _ _ => by
    simp only [Pi.zero_apply, zero_mul]
    exact MemLp.zero⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.add_apply, a2, b2]
    · simp only [Pi.add_apply, a3, b3]
    · have h := (a4 u hu hc).add (b4 u hu hc)
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨a1.const_smul c, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.smul_apply, a2]
    · simp only [Pi.smul_apply, a3]
    · have h := (a4 u hu hc).const_smul c
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem zero_of_ae (hB : Basic) (hA : AeEq) (hn : 1 ≤ n) (D : Dom E n 0) {f : GA E n → ℂ} (hf : Slab D f)
    (h : ∀ᵐ x ∂D.ν, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0) : f = 0 := by
  obtain ⟨hl, hm, -⟩ := hB E n hn
  have hinv : Inv (fun x : H E n 0 => f x.1) := by
    rintro ⟨_, ⟨p, q⟩, rfl⟩ x
    exact hf.2.1 p x.1
  have key := hA E n D (fun x => f x.1) (fun _ => 0) _ (hf.1.comp continuous_fst) continuous_const hinv
    (fun _ _ => rfl) isOpen_Ioo h
  funext g
  have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hm, hl, neg_add_cancel]
    constructor <;> norm_num
  exact (hf.2.2.1 _ g).symm.trans (key _ h0)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.formEx_pf :
    Basic → AeEq → WtInd → FormEx := by
  intro hB hA hW E _ _ _ n hn D
  obtain ⟨w, wc, ws, w0, wp, w1⟩ := weight_ex
  have uc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp wc
  have us : HasCompactSupport fun s => (w s : ℂ) := ws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have u1 : ∫ s, (w s : ℂ) = 1 := by rw [integral_complex_ofReal, w1, Complex.ofReal_one]
  have hI : ∀ a b : slabSp D, Integrable
      (fun x : H E n 0 => starRingEnd ℂ (a.1 x.1) * b.1 x.1 * (w (ldet x) : ℂ)) D.ν :=
    fun a b => (hW E n hn D a.1 b.1 a.2 b.2 _ uc us).1
  let B : slabSp D →ₗ⋆[ℂ] slabSp D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => prW D (fun s => (w s : ℂ)) a.1 b.1)
      (fun a a' b => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a' b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        ring)
      (fun a b b' => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a b')]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring)
  have hBv : ∀ a b, B a b = prW D (fun s => (w s : ℂ)) a.1 b.1 := fun _ _ => rfl
  refine ⟨slabSp D, B, fun _ => Iff.rfl, fun a b => ?_, fun a ha => ?_, fun a b u hu hc => ?_, fun g hg a => ⟨?_, ?_⟩⟩
  · rw [hBv, hBv, prW, prW, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have he : ∀ x : H E n 0, starRingEnd ℂ (a.1 x.1) * a.1 x.1 * (w (ldet x) : ℂ) =
        ((Complex.normSq (a.1 x.1) * w (ldet x) : ℝ) : ℂ) := fun x => by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    have hi : Integrable (fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x)) D.ν := by
      have h := (hI a a).re
      simp only [he, RCLike.re_to_complex, Complex.ofReal_re] at h
      exact h
    have hnn : 0 ≤ fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x) :=
      fun x => mul_nonneg (Complex.normSq_nonneg _) (w0 _)
    rw [hBv, prW]
    simp only [he]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ha (Subtype.ext ?_)
    refine zero_of_ae hB hA hn D a.2 ?_
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0.symm] with x hx hI'
    exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right (wp _ hI'))
  · exact (hW E n hn D a.1 b.1 a.2 b.2 u hu hc).2.1 _ uc us u1
  · exact ((hW E n hn D a.1 a.1 a.2 a.2 _ uc us).2.2 g hg).1
  · intro a' b b' h1 h2
    rw [hBv, hBv, funext h1, funext h2]
    exact ((hW E n hn D a.1 b.1 a.2 b.2 _ uc us).2.2 g hg).2
