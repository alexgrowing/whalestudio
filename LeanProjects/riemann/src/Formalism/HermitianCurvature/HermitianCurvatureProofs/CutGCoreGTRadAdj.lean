import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_inner_sum (A₁ A₂ : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A₁) (B.hsVec A₂) =
      ∑ i, inner ℂ (A₁ (stdOrthonormalBasis ℂ Wq i)) (A₂ (stdOrthonormalBasis ℂ Wq i)) := by
  simp [B.hsVec, PiLp.inner_apply]

end hs

section int

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem int_pair {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ)
    (Θ₁ Θ₂ : Q.RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Qx5.Dp k r z z') (v : Wq)
    (h0 : ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K →
      inner ℂ ((Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v) ((Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v) = 0) :
    Integrable (fun x : Mt k r => inner ℂ ((Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)
      ((Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)) μ := by
  have c1 := Qx5.smoothLev_continuousOn (Qx5.slice_smooth Θ₁.2 hc)
  have c2 := Qx5.smoothLev_continuousOn (Qx5.slice_smooth Θ₂.2 hc)
  exact Qx5.integrable_cpt hμ (p := fun g => inner ℂ ((Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v)
    ((Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v)) hK hKD
    ((c1.clm_apply continuousOn_const).inner (c2.clm_apply continuousOn_const)) h0

theorem int_hs_sum [FiniteDimensional ℂ Wq] {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ)
    (Θ₁ Θ₂ : Q.RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Qx5.Dp k r z z')
    (h0 : ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K →
      (Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = 0 ∨ (Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    (∫ x : Mt k r, inner ℂ (B.hsVec ((Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
      (B.hsVec ((Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ) =
      ∑ i, ∫ x : Mt k r, inner ℂ ((Θ₁ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq i))
        ((Θ₂ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq i)) ∂μ := by
  simp_rw [hs_inner_sum]
  refine integral_finsetSum _ fun i _ => int_pair hμ Θ₁ Θ₂ hc hK hKD _ fun g hg hgK => ?_
  rcases h0 g hg hgK with h | h <;> simp [h]

end int

section weight

theorem zw_ann (P : M.Par) (hTT : 0 < P.TT) (ψ : ℂ → ℂ) :
    (∫ ζ, (B2.zWeight P.k P.T P.T' ζ : ℂ) * ψ ζ) =
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) * ψ ζ := by
  have hm : MeasurableSet (Ann P) := measurableSet_lt measurable_const Complex.continuous_normSq.measurable
  rw [← integral_indicator hm]
  refine integral_congr_ae ?_
  filter_upwards [JCx2.rb_ae_ne_circle hTT] with ζ hζ
  by_cases h : ζ ∈ Ann P
  · rw [Set.indicator_of_mem h]
    have h' : P.TT < Complex.normSq ζ := h
    have hle : P.T * P.T' ≤ Complex.normSq ζ := le_of_lt h'
    unfold wR B2.zWeight
    rw [if_pos hle, Real.sq_sqrt (pow_nonneg (sub_nonneg.2 (le_of_lt (show P.TT < Complex.normSq ζ from h))) _)]
    rfl
  · rw [Set.indicator_of_notMem h, JCx2.rb_zWeight_zero_of_not (k := P.k) (T := P.T) (T' := P.T') h hζ]
    simp

end weight

theorem radial_adjoint_identity_holds : GTRadAdj := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH Y a b c hc Φ Ψ hKz
  obtain ⟨Kz, hKzc, hKzA, hKz0⟩ := hKz
  have hP := hH.1
  have hT : Tz P.k P.r Bs.z = P.T := hP.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hP.2.2.2.2.1
  have hAnn : ∀ ζ : ℂ, ζ ∈ Ann P ↔ Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ
    rw [hT, hT']
    rfl

  have hmem := Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k P.r Bs.z Bs.z' Bs.μsec Bs.z_mem Bs.z'_mem Bs.sec
  have hdom : ∀ ζ : ℂ, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ →
      ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
        (c, h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h') ∈ Q.DomR P.k P.r Bs.z Bs.z' := by
    intro ζ hζ h hh h' hh'
    obtain ⟨hm, hherm⟩ := hmem ζ hζ h hh h' hh'
    refine ⟨hc, JCx2.rb_uwb_glev hm, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last]
    erw [hherm]
    exact sub_pos.2 hζ
  have hdom0 : ∀ ζ : ℂ, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ →
      (c, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' := by
    intro ζ hζ
    have := hdom ζ hζ 1 (Qx8.uw_one _) 1 (Qx8.uw_one _)
    simpa using this

  let SW : Set (Mt P.k P.r) := {x | (Matrix.of x : Q.Mx P.k P.r) ∈ UWset P.k P.r Bs.z}
  let SW' : Set (Mt P.k P.r) := {x | (Matrix.of x : Q.Mx P.k P.r) ∈ UWset P.k P.r Bs.z'}
  let F : ℂ × (Mt P.k P.r × Mt P.k P.r) → Mt P.k P.r := fun p =>
    JCx2.rbMul (JCx2.rbMul (p.2.1, JCx2.rbEf P.k P.r Bs.μsec p.1), p.2.2)
  have hF : ∀ p : ℂ × (Mt P.k P.r × Mt P.k P.r),
      (Matrix.of (F p) : Q.Mx P.k P.r) = Matrix.of p.2.1 * NF.muZ P.k P.r Bs.μsec p.1 * Matrix.of p.2.2 := fun p => rfl
  have hSW : IsCompact SW := Formalism.FourierDecayAlt.P.B2x3.compactW P.k P.r Bs.z Bs.z_mem Bs.T_pos
  have hSW' : IsCompact SW' := Formalism.FourierDecayAlt.P.B2x3.compactW P.k P.r Bs.z' Bs.z'_mem Bs.T'_pos
  have hS : IsCompact (Kz ×ˢ (SW ×ˢ SW')) := hKzc.prod (hSW.prod hSW')
  have hEc : ContinuousOn (JCx2.rbEf P.k P.r Bs.μsec) (Ann P) := by
    have h1 := JCx2.rb_contOn_E (k := P.k) (r := P.r) (T := Tz P.k P.r Bs.z) (T' := Tz P.k P.r Bs.z')
      (μsec := Bs.μsec) fun i j => (Bs.sec.1 i j).continuousOn
    refine h1.mono fun ζ hζ => ?_
    exact (hAnn ζ).1 hζ
  have hFc : ContinuousOn F (Kz ×ˢ (SW ×ˢ SW')) := by
    have hA : ContinuousOn (fun p : ℂ × (Mt P.k P.r × Mt P.k P.r) =>
        (p.2.1, JCx2.rbEf P.k P.r Bs.μsec p.1)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (continuous_fst.comp continuous_snd).continuousOn.prodMk
        (hEc.comp continuousOn_fst fun p hp => hKzA hp.1)
    have hB : ContinuousOn (fun p : ℂ × (Mt P.k P.r × Mt P.k P.r) =>
        (JCx2.rbMul (p.2.1, JCx2.rbEf P.k P.r Bs.μsec p.1), p.2.2)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hA).prodMk
        (continuous_snd.comp continuous_snd).continuousOn
    exact Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hB
  let K' : Set (Q.Mx P.k P.r) := F '' (Kz ×ˢ (SW ×ˢ SW'))
  have hK'c : IsCompact K' := hS.image_of_continuousOn hFc
  have hinvinv : ∀ x : Mt P.k P.r, (Matrix.of x : Q.Mx P.k P.r) ∈ UWset P.k P.r Bs.z →
      ((Matrix.of x : Q.Mx P.k P.r)⁻¹)⁻¹ = Matrix.of x := fun x hx =>
    Matrix.inv_eq_right_inv (Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hx)
  have hK'D : K' ⊆ Qx5.Dp P.k P.r Bs.z Bs.z' := by
    rintro g ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩
    have hζ := (hAnn p.1).1 (hKzA hp1)
    have hd := hdom p.1 hζ ((Matrix.of p.2.1 : Q.Mx P.k P.r)⁻¹) (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp2)
      (Matrix.of p.2.2) hp3
    rw [hinvinv _ hp2] at hd
    show (Matrix.of (F p) : Q.Mx P.k P.r) ∈ Qx5.Dp P.k P.r Bs.z Bs.z'
    rw [hF]
    exact hd.2.2

  have hvan : ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), g ∉ K' →
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := by
    intro g hg hgK
    by_cases hG : 0 < Q.GGl P.k P.r Bs.z Bs.z' g
    · have hu := P5.Rad.glev_last_uwb hg
      have hζA : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' <
          Complex.normSq (herm (Hpk P.k P.r) (g.mulVec Bs.z') Bs.z) := by
        unfold Q.GGl at hG
        rw [P5.Rad.zetaL_last] at hG
        linarith
      obtain ⟨h, hh, h', hh', hgeq⟩ := Formalism.FourierDecayAlt.P.b2_rank_one_coord P.k P.r Bs.z Bs.z' Bs.μsec Bs.k_pos
        Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec g hu hζA
      have hζK : herm (Hpk P.k P.r) (g.mulVec Bs.z') Bs.z ∉ Kz := by
        intro hK
        apply hgK
        refine ⟨(herm (Hpk P.k P.r) (g.mulVec Bs.z') Bs.z, ((h⁻¹ : Q.Mx P.k P.r), (h' : Q.Mx P.k P.r))),
          ⟨hK, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh, hh'⟩, ?_⟩
        show (Matrix.of (F _) : Q.Mx P.k P.r) = g
        rw [hF]
        exact hgeq.symm
      obtain ⟨e1, e2⟩ := hKz0 _ ((hAnn _).2 hζA) hζK
      have hd := hdom0 _ hζA
      have q1 := Φ.2.2.2 _ hd _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh) _ hh'
      have q2 := Ψ.2.2.2 _ hd _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh) _ hh'
      rw [hgeq]
      constructor
      · erw [q1, e1]
        simp
      · erw [q2, e2]
        simp
    · have hnd : (c, g) ∉ Q.DomR P.k P.r Bs.z Bs.z' := fun hd => hG hd.2.2
      exact ⟨Φ.2.1 (c, g) hnd, Ψ.2.1 (c, g) hnd⟩

  obtain ⟨μ, hμb⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists P.k P.r
  have hμ : B.IsHaarOn (Q.Glev P.k P.r (Fin.last P.r)) μ := by
    rw [← JCx2.rb_uwb_eq]
    exact hμb

  have hadj : (∫ x : Mt P.k P.r, inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
        (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ) =
      ∫ x : Mt P.k P.r, inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
        (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ := by
    rw [int_hs_sum hμ _ _ hc hK'c hK'D fun g hg hgK => Or.inr (hvan g hg hgK).2,
      int_hs_sum hμ _ _ hc hK'c hK'D fun g hg hgK => Or.inl (hvan g hg hgK).1]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Formalism.FourierDecayAlt.P.actual_adjointness Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X μ hμ Φ Ψ c hc
      ⟨K', hK'c, hK'D, hvan⟩ Y a b _

  obtain ⟨C, hC, hmap⟩ := JCx2.rb_map Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec hμb Bs.haarW Bs.haarW'
  have hfW : IsFiniteMeasure Bs.μW :=
    Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  have hfW' : IsFiniteMeasure Bs.μW' :=
    Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  have hm : 0 < (Bs.μW.prod Bs.μW').real Set.univ := by
    rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    refine mul_pos (ENNReal.toReal_pos ?_ (measure_ne_top _ _)) (ENNReal.toReal_pos ?_ (measure_ne_top _ _))
    · exact Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero
    · exact Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero
  have hC1 : ((C : ℝ) * (Bs.μW.prod Bs.μW').real Set.univ) ≠ 0 :=
    (mul_pos (by exact_mod_cast hC) hm).ne'
  have hTT : 0 < P.TT := by
    unfold M.Par.TT
    rw [← hT, ← hT']
    exact mul_pos Bs.T_pos Bs.T'_pos
  have hrad : ∀ Θ₁ Θ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∫ x : Mt P.k P.r, inner ℂ (B.hsVec ((Θ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
        (B.hsVec ((Θ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ) =
      (((C : ℝ) * (Bs.μW.prod Bs.μW').real Set.univ : ℝ) : ℂ) *
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Θ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Θ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) := by
    intro Θ₁ Θ₂
    rw [JCx2.rb_integral Bs.T_pos Bs.T'_pos Bs.sec Bs.haarW Bs.haarW' hmap (fun x : Mt P.k P.r => inner ℂ (B.hsVec ((Θ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x)))
        (B.hsVec ((Θ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x)))) (JCx2.rb_pair_sm Θ₂ Θ₁ c)
      (fun ζ => inner ℂ (B.hsVec ((Θ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
        (B.hsVec ((Θ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))) ?_]
    · congr 1
      rw [hT, hT']
      exact zw_ann P hTT _
    · intro ζ hζ x y hx hy
      have hPsi : (Matrix.of (JCx2.rbPsi P.k P.r (Tz P.k P.r Bs.z) (Tz P.k P.r Bs.z') Bs.μsec (ζ, (x, y))) :
          Q.Mx P.k P.r) = (Matrix.of x)⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * Matrix.of y := by
        rw [JCx2.rb_Psi_eq hζ]
        rfl
      have hd := hdom0 ζ hζ
      have hinv := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hx
      show inner ℂ (B.hsVec ((Θ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of (JCx2.rbPsi P.k P.r (Tz P.k P.r Bs.z)
          (Tz P.k P.r Bs.z') Bs.μsec (ζ, (x, y))))))
        (B.hsVec ((Θ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of (JCx2.rbPsi P.k P.r (Tz P.k P.r Bs.z)
          (Tz P.k P.r Bs.z') Bs.μsec (ζ, (x, y)))))) = _
      rw [hPsi]
      erw [Θ₁.2.2.2 _ hd _ hinv _ hy, Θ₂.2.2.2 _ hd _ hinv _ hy]
      exact Formalism.FourierDecayAlt.P.B7.al_hs_inv _ (Bs.π_unitary _ hinv) _ (Bs.π'_unitary _ hy) _ _
  rw [hrad, hrad] at hadj
  exact mul_left_cancel₀ (by exact_mod_cast hC1) hadj

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_adjoint_identity_holds : GTRadAdj := RadAdj.radial_adjoint_identity_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
