import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartThetaEquivariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActOFIotaVFEqIotaVFMulVec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW.TauSpanIdentities
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem piWF_ratWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := by
  funext p
  exact PositivityTheory.ThKW.RealC.theta_inc (C.inf p.2) _
theorem continuous_piWF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS) (nT := nT) θ) :=
  continuous_pi fun p => (PositivityTheory.ThKW.RealC.continuous_theta (C.inf p.2)).comp
    ((continuous_apply p.1.2).comp (continuous_apply p.1.1))
theorem beta_iota_right_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).1
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_left, h0, zero_add,
    _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem beta_iota_left_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).2
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_right, h0, zero_add,
    _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem piWF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x := by
  have hx := finIdem_add_iota C.chart x
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.actOF_add, piWF_add, piWF_of_fin (actOF_fin g h (finIdem_smul_fin x)), zero_add,
    _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart g h, piWF_iotaVF C.chart]
theorem psi_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 := by
  rw [symplOHF_rat]
  exact C.good.std.2.1 _
theorem symplOF_actOF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF C.hS]
theorem gamQF_eq_one_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔
      ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z := by
  have hx : ratWF (F := F) x = finIdem F E • ratWF (F := F) x + iotaVF ι (infRatF (tauB B) x) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) x); rwa [_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_ratWF_k C] at this
  have hy : ratWF (F := F) y = finIdem F E • ratWF (F := F) y + iotaVF ι (infRatF (tauB B) y) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) y); rwa [_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_ratWF_k C] at this
  have cross : ∀ (a : WOF F E nS nT) (b : IxF F nS nT → ℂ), a.map (infPartF F E) = 0 →
      symplOHF σ JS JT ξ₀ a (iotaVF ι b) = 0 ∧ symplOHF σ JS JT ξ₀ (iotaVF ι b) a = 0 :=
    fun a b ha => GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ a (iotaVF ι b) ha (real_iotaVF C.chart b)
  have hr := _root_.PositivityTheory.ThKW.TauSpanIdentities.psi_rat_k C x y
  rw [hx, hy, GlobalTheory.RealWeilF.symplOHF_add_left, GlobalTheory.RealWeilF.symplOHF_add_right, GlobalTheory.RealWeilF.symplOHF_add_right,
    (cross _ _ (finIdem_smul_fin _)).1, (cross _ _ (finIdem_smul_fin _)).2, add_zero, zero_add,
    AddChar.map_add_eq_mul, _root_.PositivityTheory.ThKW.TauSpanIdentities.beta_iota_right_k C, piWF_iotaVF C.chart] at hr
  set om := omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y)
  set P := B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y))
  have hg : gamQF σ JS JT ξ₀ B.ψ x y = P * P := by
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    rw [symplOF_eq_add, AddChar.map_add_eq_mul]
  have hP : P = Complex.exp (Real.pi * Complex.I * (om : ℂ)) := by
    calc P = P * (Complex.exp (-(Real.pi * Complex.I) * (om : ℂ)) * Complex.exp (Real.pi * Complex.I * (om : ℂ))) := by
          rw [← Complex.exp_add, show -(Real.pi * Complex.I) * (om : ℂ) + Real.pi * Complex.I * (om : ℂ) = 0 by ring,
            Complex.exp_zero, mul_one]
      _ = _ := by rw [← mul_assoc, hr, one_mul]
  rw [hg, hP, ← Complex.exp_add, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 : ℂ) * (Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    have : (om : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩
section Lin
variable {κ : Type} [Fintype κ]
end Lin
theorem sig_sig_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
theorem gamQF_eq_one_iff'_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n := by
  haveI : IsTotallyReal F := C.good.cm.1
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : gamQF σ JS JT ξ₀ B.ψ x y =
      B.ψ (pairA F 0 (algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)))) := by
    have := LatC.sympl_ft (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (_root_.PositivityTheory.ThKW.TauSpanIdentities.sig_sig_k C.good) 1 1 x y
    rw [one_mul, one_mul] at this
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    exact congrArg B.ψ this
  have h2 : ∀ t : F, pairA F 0 (algebraMap F (Af F) t) = algebraMap F (AF F) t + pairA F (-(algebraMap F (Ainf F) t)) 0 := by
    intro t
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) t + -(algebraMap F (Ainf F) t)
      rw [add_neg_cancel]
    · show algebraMap F (Af F) t = algebraMap F (Af F) t + 0
      rw [add_zero]
  have h3 : ∀ t : F, B.ψ (pairA F (-(algebraMap F (Ainf F) t)) 0) =
      Complex.exp (2 * Real.pi * Complex.I * algebraMap ℚ ℂ (Algebra.trace ℚ F t)) := by
    intro t
    have hw : ∀ w, θ w ((-(algebraMap F (Ainf F) t)) ⊗ₜ[F] (1 : E)) = -(w.embedding t) := by
      intro w
      have e : (algebraMap F (Ainf F) t) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E t := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [TensorProduct.neg_tmul, map_neg, e, (C.inf w).1]
      exact congrArg Neg.neg (RingHom.congr_fun (B.emb w).2 t)
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA C.good.std, ← GlobalTheory.StdCharWeilDatum.sum_infFam B θ C.inf, trace_places]
    congr 1
    simp only [hw, Finset.sum_neg_distrib]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, C.good.std.2.1, one_mul, h3, Complex.exp_eq_one_iff, Algebra.trace_trace]
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y)) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by linear_combination hn)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h4
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, map_intCast]; ring⟩
section Span
theorem span_tau_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) = ⊤ := by
  haveI : IsTotallyComplex E := hB.cm.2.1
  have hall : ∀ z ∈ Submodule.span ℝ (Set.range (mixedEmbedding E)),
      Lm B z ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨e, ?_⟩
      funext w
      show (B.emb w).1 e = cw B w ((wE B w).embedding e)
      rw [cw_emb]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have htop : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq (mixedEmbedding.latticeBasis E).span_eq.symm) (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (mixedEmbedding.latticeBasis_apply E i).symm⟩
  rw [eq_top_iff]
  rintro f -
  let z : mixedEmbedding.mixedSpace E :=
    (0, fun W => cw B (W.1.comap (algebraMap F E)) (f (W.1.comap (algebraMap F E))))
  have hz : Lm B z = f := by
    funext w
    show cw B w (cw B ((wE B w).comap (algebraMap F E)) (f ((wE B w).comap (algebraMap F E)))) = f w
    rw [wE_comap, cw_cw]
  rw [← hz]
  exact hall z (htop ▸ Submodule.mem_top)
theorem span_infRatF_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ := by
  set V := Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B)))
  have key : ∀ (q : Fin nT × Fin nS) (g : InfinitePlace F → ℂ),
      (fun p : IxF F nS nT => if p.1 = q then g p.2 else 0) ∈ V := by
    intro q g
    have hg : g ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
      rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.span_tau_k hB]; trivial
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨Matrix.of fun a b => if (a, b) = q then e else 0, ?_⟩
      funext p
      show (B.emb p.2).1 (if (p.1.1, p.1.2) = q then e else 0) = if p.1 = q then (B.emb p.2).1 e else 0
      by_cases h : p.1 = q
      · rw [if_pos h, if_pos (by rw [← h])]
      · rw [if_neg h, if_neg (by intro h'; exact h (by rw [← h'])), map_zero]
    | zero =>
      convert V.zero_mem using 1
      funext p
      split_ifs <;> rfl
    | add g g' _ _ hg hg' =>
      convert V.add_mem hg hg' using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
    | smul c g _ hg =>
      convert V.smul_mem c hg using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ q : Fin nT × Fin nS, (fun p : IxF F nS nT => if p.1 = q then v (q, p.2) else 0) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [hv]
  exact V.sum_mem fun q _ => key q (fun w => v (q, w))
end Span
end PositivityTheory.ThKW.TauSpanIdentities
end
end
