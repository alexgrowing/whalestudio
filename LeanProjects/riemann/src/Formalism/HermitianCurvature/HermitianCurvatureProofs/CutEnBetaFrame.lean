import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toSm_val_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) :
    ((MA.toSm P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = u := by
  unfold MA.toSm; rw [dif_pos h]

theorem hsVec_sum_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → (W →L[ℂ] V)) :
    B.hsVec (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • B.hsVec (e ρ) := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • Formalism.FourierDecayAlt.P.JFxI.hsVecL (e ρ)
  rw [map_sum]
  simp only [map_smul]

theorem parseval {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (e : ι → (W →L[ℂ] V))
    (X Y : W →L[ℂ] V) (hX : X = ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) • e ρ) :
    inner ℂ (B.hsVec Y) (B.hsVec X) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) * conj (inner ℂ (B.hsVec (e ρ)) (B.hsVec Y)) := by
  conv_lhs => rw [hX]
  rw [hsVec_sum_smul, inner_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_smul_right, inner_conj_symm]

theorem jgq_contDiffOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    {J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
    (hJ : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ContDiffOn ℝ ∞ (fun x => J (B.gq (T v).base x)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hGl : ∀ x ∈ JF.QDom S.G.k S.G.r Db.z Db.z', B.gq Db x ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun x hx =>
    om_sub' (Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db x hx)
  have hgq : ContDiffOn ℝ ∞ (fun x => B.gq Db x) (JF.QDom S.G.k S.G.r Db.z Db.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Db n
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ.1 _ (hGl x₀ (hQ x₀ hx₀))
  refine ⟨JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U,
    hgq.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open _ _) hU, ⟨hQ x₀ hx₀, hgU⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun x => F (B.gq Db x))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT ∩ (JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U)) :=
    hF.comp (hgq.mono fun x hx => hx.2.1) fun x hx => hx.2.2
  exact hc.congr fun x hx => hJF _ hx.2.2 (hGl x hx.2.1).1

theorem beta_frame_identity_holds : BetaFrame := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hplace e hFr J₁ hJ₁ J₂ hJ₂ hN₁ hN₂
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs
  have hQm : MeasurableSet Qs := (MA.Qset_open _ _).measurableSet
  set W : (Fin S.G.r → ℂ) × ℂ → ℝ := bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') with hWdef
  have hW0 : ∀ x, 0 ≤ W x := fun x => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ x

  have hW : ∀ x ∈ Qs, W x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
    intro x hx
    have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
      rw [hTT]; exact le_of_lt hx.2
    rw [hWdef]
    unfold bcWeight
    rw [if_pos hle]
    unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
    rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
      have := l.isLt
      simp only [MA.Mdim]; omega
    have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
    have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
    rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
      pow_succ]
    field_simp

  have hval : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v), ∀ ρ,
      ((trJ S T v e J ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) =
        fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Db q.1))) := fun J hJ ρ =>
    toSm_val_of_mem (D.parOf S v) (trace_smoothness E Wp Wq S T v hplace e hFr J hJ ρ)

  have hR : ∀ ρ, MA.ip0 (trJ S T v e J₁ ρ) (trJ S T v e J₂ ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e J₁ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e J₂ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval J₁ hJ₁, hval J₂ hJ₂]
    rw [dif_pos (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)
  have hU : ∀ (J) (hJ : J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v)),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') (fun q => B.hsVec (J (B.gq Db q))) ≠ ⊤ →
      IntegrableOn (fun x => W x * ‖B.hsVec (J (B.gq Db x))‖ ^ 2) Qs := by
    intro J hJ hN
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      (((hcont J hJ).norm.pow 2).aestronglyMeasurable hQm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    exact lt_of_le_of_lt (setLIntegral_le_lintegral Qs _) (lt_top_iff_ne_top.2 hN)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))))) Qs := by
    intro ρ
    refine Integrable.mono' ((hU J₁ hJ₁ hN₁).add (hU J₂ hJ₂ hN₂)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        ((((heC ρ).inner (hcont J₁ hJ₁)).mul ((heC ρ).inner (hcont J₂ hJ₂)).star).aestronglyMeasurable hQm)
    · refine ae_restrict_of_forall_mem hQm fun x hx => ?_
      have he1 : ‖B.hsVec (e ρ x.2)‖ ≤ 1 := by
        have h1 : inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (e ρ x.2)) = (1 : ℂ) := by
          simpa using (hFr.2 x.2 hx.2).2.1 ρ ρ
        rw [inner_self_eq_norm_sq_to_K] at h1
        have h2' : ((‖B.hsVec (e ρ x.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
        have h2 : ‖B.hsVec (e ρ x.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
        nlinarith [norm_nonneg (B.hsVec (e ρ x.2))]
      have ha : ∀ J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J (B.gq Db x)))‖ ≤ ‖B.hsVec (J (B.gq Db x))‖ := fun J =>
        (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (J (B.gq Db x)))])
      have hn1 := ha J₁
      have hn2 := ha J₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖ ≤
            ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))),
          norm_nonneg (B.hsVec (J₁ (B.gq Db x))), norm_nonneg (B.hsVec (J₂ (B.gq Db x))),
          sq_nonneg (‖B.hsVec (J₁ (B.gq Db x))‖ - ‖B.hsVec (J₂ (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by ring

  unfold MA.ipA
  simp_rw [hR]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold betaBig
  have hae : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ Qs →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (J₂ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (J₁ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db] with x hx hxQ
    rcases hx with hx | hx
    · exfalso
      apply hxQ
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [hTT] at h2
      exact h2
    · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hX := (hFr.2 x.2 hx.2).2.2 (J₁ (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace J₁ hJ₁ x hx)
  exact parseval (fun ρ => e ρ x.2) (J₁ (B.gq Db x)) (J₂ (B.gq Db x)) hX

end Formalism.FourierDecayAlt.P.CutMP.En
