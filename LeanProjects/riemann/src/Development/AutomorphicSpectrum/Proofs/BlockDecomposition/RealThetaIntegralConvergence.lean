import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealWhittakerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormRealWhittakerTorusLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylTransposeInvIwasawaRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingIwasawaRealOrthogonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Weyl3TransposeInvEmbeddingIwasawaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfSmoothRealGL3Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealEmbeddingGL3Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealTransposeInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIwasawaRealParametrizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealRotationOrthogonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaRealOfDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormZetaIntegrandDecayBoundStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.RealPlace

abbrev mE (n : ℤ) : ℝ := ((n.natAbs + 1 : ℕ) : ℝ) / 2

theorem cont_chR (s : ℂ) : Continuous (chR false s) := by
  have h : Continuous (fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (Units.continuous_val.abs)
  have h2 : Continuous (fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ) ^ s) := by
    refine h.cpow continuous_const fun a => Or.inl ?_
    simpa using a.ne_zero
  have e : chR false s = fun a : ℝˣ => (((|(a : ℝ)| : ℝ)) : ℂ) ^ s := by
    funext a
    simp [chR]
  rw [e]
  exact h2

theorem cont_rI {W₃ : GL (Fin 3) ℝ → ℂ} {W₂ : GL (Fin 2) ℝ → ℂ} (c3 : Continuous W₃) (c2 : Continuous W₂) (s : ℂ) :
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W₃ W₂ s p.1 p.2.1 p.2.2) := by
  unfold rI
  have h := GlobalTheory.T.continuous_iwasawa_real_parametrization
  have h1 : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => p.2.1) := continuous_snd.fst
  exact (((c3.comp (GlobalTheory.T.continuous_real_embedding_GL3.comp h)).mul (c2.comp h)).mul ((cont_chR _).comp h1)).mul ((cont_chR _).comp h2)

theorem cont_iwR {W₃ : GL (Fin 3) ℝ → ℂ} {W₂ : GL (Fin 2) ℝ → ℂ} (c3 : Continuous W₃) (c2 : Continuous W₂)
    (s : ℂ) (ε : Bool) : Continuous (GL2LocalData.iwR W₃ W₂ s ε) := by
  have h : Continuous (fun p : ℝˣ × ℝˣ × ℝ => ((p.1, p.2.1, GL2LocalData.kR p.2.2 ε) : ℝˣ × ℝˣ × GL (Fin 2) ℝ)) :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk ((GlobalTheory.T.continuous_real_rotation_orthogonal ε).1.comp continuous_snd.snd))
  have h2 := (cont_rI c3 c2 s).comp h
  have e : GL2LocalData.iwR W₃ W₂ s ε = (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W₃ W₂ s p.1 p.2.1 p.2.2) ∘
      (fun p : ℝˣ × ℝˣ × ℝ => ((p.1, p.2.1, GL2LocalData.kR p.2.2 ε) : ℝˣ × ℝˣ × GL (Fin 2) ℝ)) := by
    funext p
    simp only [GL2LocalData.iwR, rI, Function.comp]
  rw [e]
  exact h2

theorem int_core (W₃ : GL (Fin 3) ℝ → ℂ) (W₂ : GL (Fin 2) ℝ → ℂ) (c3 : Continuous W₃) (c2 : Continuous W₂)
    (T : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (h3 : ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 →
      ‖W₃ (GL2LocalData.emR (dg2 (a * b) b * k))‖ ≤
        C / (|(a : ℝ)| * |(b : ℝ)|) ^ T / ((1 + |(a : ℝ)|) * (1 + |(b : ℝ)|)) ^ N)
    (h2 : ∀ (a b : ℝˣ) (k : GL (Fin 2) ℝ), k.val * k.valᵀ = 1 → ‖W₂ (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ m)
    (s : ℂ) (hs : (T : ℝ) + 3 < s.re) (ε : Bool) : Integrable (GL2LocalData.iwR W₃ W₂ s ε) GL2LocalData.mIwR := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (s.re - 3 / 2 + m - T) (2 * s.re - 1 - T))
  have hN1 : s.re - 3 / 2 + m - T < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 * s.re - 1 - T < N := lt_of_le_of_lt (le_max_right _ _) hN
  obtain ⟨C, hC⟩ := h3 N
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  refine GlobalTheory.T.integrable_iwasawa_real_of_decay _ C (s.re - 3 / 2 + m - T) (2 * s.re - 1 - T) N (cont_iwR c3 c2 s ε).aestronglyMeasurable
    (by linarith) (by linarith) hN1 hN2 ?_
  intro a b θ
  have ha : 0 < |(a : ℝ)| := abs_pos.2 a.ne_zero
  have hb : 0 < |(b : ℝ)| := abs_pos.2 b.ne_zero
  have ho := (GlobalTheory.T.continuous_real_rotation_orthogonal ε).2 θ
  have := GlobalTheory.T.norm_zeta_integrand_decay_bound (W₃ (GL2LocalData.emR (dg2 (a * b) b * GL2LocalData.kR θ ε))) (W₂ (dg2 (a * b) b * GL2LocalData.kR θ ε)) s
    |(a : ℝ)| |(b : ℝ)| C m T N ha hb (hC a b _ ho) (h2 a b _ ho)
  simpa [GL2LocalData.iwR, chR] using this

theorem cont_thR (n : ℤ) (t : ℝ) : Continuous (thR n t) := by
  have hd : Continuous (fun g : GL (Fin 2) ℝ => |(g.val).det|) :=
    (Continuous.matrix_det Units.continuous_val).abs
  have hd' : Continuous (fun g : GL (Fin 2) ℝ => (((|(g.val).det| : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp hd
  unfold thR
  refine (GlobalTheory.T.continuous_real_whittaker n).mul (hd'.cpow continuous_const ?_)
  intro g
  refine Or.inl ?_
  simpa using (g.det.ne_zero)

theorem norm_thR_le (n : ℤ) (t : ℝ) (a b : ℝˣ) (k : GL (Fin 2) ℝ) (hk : k.val * k.valᵀ = 1) :
    ‖thR n t (dg2 (a * b) b * k)‖ ≤ |(a : ℝ)| ^ mE n := by
  have hdet : 0 < |((dg2 (a * b) b * k).val).det| := abs_pos.2 ((dg2 (a * b) b * k).det.ne_zero)
  unfold thR
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hdet]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, Real.rpow_zero, mul_one]
  refine (GlobalTheory.T.norm_real_whittaker_torus_le n a b k hk).trans ?_
  have h1 : Real.exp (-(2 * Real.pi * |(a : ℝ)|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h0 := abs_nonneg (a : ℝ)
    have hp := Real.pi_pos
    nlinarith [mul_nonneg hp.le h0]
  exact mul_le_of_le_one_right (by positivity) h1

theorem main : ∀ (k : ℕ) (V : Submodule ℂ (GL (Fin 3) ℝ → ℂ)) (E : Fin 3 → Fin 3 → Module.End ℂ V), WhR k V E → ∀ W ∈ V, ∀ (n : ℤ) (t : ℝ),
  (∀ s : ℂ, Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI W (thR n t) s p.1 p.2.1 p.2.2) ∧
    Continuous (fun p : ℝˣ × ℝˣ × GL (Fin 2) ℝ => rI (GL2LocalData.dW3R W) (GL2LocalData.dW2R (thR n t)) s p.1 p.2.1 p.2.2)) ∧
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ ε : Bool, Integrable (GL2LocalData.iwR W (thR n t) s ε) GL2LocalData.mIwR ∧
    Integrable (GL2LocalData.iwR (GL2LocalData.dW3R W) (GL2LocalData.dW2R (thR n t)) s ε) GL2LocalData.mIwR := by
  intro k V E h W hW n t
  have cW : Continuous W := GlobalTheory.T.continuous_of_smooth_real_GL3 W (h.smooth W hW)
  have cT : Continuous (thR n t) := cont_thR n t
  have cW' : Continuous (GL2LocalData.dW3R W) := by
    unfold GL2LocalData.dW3R
    exact cW.comp (continuous_const.mul (GlobalTheory.T.continuous_real_transposeInv 3))
  have cT' : Continuous (GL2LocalData.dW2R (thR n t)) := by
    unfold GL2LocalData.dW2R
    exact cT.comp (continuous_const.mul (GlobalTheory.T.continuous_real_transposeInv 2))
  refine ⟨fun s => ⟨cont_rI cW cT s, cont_rI cW' cT' s⟩, ?_⟩
  obtain ⟨T, hT⟩ := h.gauge W hW
  have hm : 0 ≤ mE n := by unfold mE; positivity
  refine ⟨(T : ℝ) + 3, fun s hs ε => ⟨?_, ?_⟩⟩
  · refine int_core W (thR n t) cW cT T (mE n) hm ?_ (fun a b k hk => norm_thR_le n t a b k hk) s hs ε
    intro N
    obtain ⟨C, hC⟩ := hT N
    refine ⟨C, fun a b k hk => ?_⟩
    obtain ⟨e1, e2⟩ := GlobalTheory.T.embedding_iwasawa_real_orthogonal a b k hk
    rw [e1]
    exact hC a b _ e2
  · refine int_core _ _ cW' cT' T (mE n) hm ?_ ?_ s hs ε
    · intro N
      obtain ⟨C, hC⟩ := hT N
      refine ⟨C, fun a b k hk => ?_⟩
      obtain ⟨o, ho, e⟩ := GlobalTheory.T.weyl3_transposeInv_embedding_iwasawa a b k hk
      have e' : GL2LocalData.dW3R W (GL2LocalData.emR (dg2 (a * b) b * k)) = W (dg (b * a) a 1 * o) := by
        unfold GL2LocalData.dW3R
        rw [e, h.cen W hW]
      rw [e']
      have := hC b a o ho
      rw [mul_comm |(b : ℝ)| |(a : ℝ)|, mul_comm (1 + |(b : ℝ)|) (1 + |(a : ℝ)|)] at this
      exact this
    · intro a b k hk
      obtain ⟨k', hk', e⟩ := GlobalTheory.T.weyl_transposeInv_iwasawa_real a b k hk
      unfold GL2LocalData.dW2R
      rw [e]
      exact norm_thR_le n t a _ k' hk'

end GlobalTheory.CompanionTheory.GL2Factorization.RealPlace
