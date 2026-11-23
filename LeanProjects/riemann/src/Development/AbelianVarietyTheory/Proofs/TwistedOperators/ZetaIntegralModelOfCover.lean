import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverHaarPushforwardSignatureUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniqueneStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.ZetaTransfer

theorem transfer {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [TopologicalSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H] {ν : Measure G} {μ : Measure H} {π : G → H} {c : NNReal} (hc : c ≠ 0)
    (hq : Topology.IsQuotientMap π) (hm : Measurable π) (hmap : Measure.map π ν = c • μ) {f : H → ℂ} {k : G → ℂ}
    (hk : Continuous k) (hf : ∀ g, f (π g) = k g) (hi : Integrable k ν) :
    Integrable f μ ∧ ∫ h, f h ∂μ = (((c : ℝ)⁻¹ : ℝ) : ℂ) * ∫ g, k g ∂ν := by
  have hcomp : f ∘ π = k := funext hf
  have hfc : Continuous f := by
    rw [hq.continuous_iff, hcomp]
    exact hk
  have hfm : AEStronglyMeasurable f (Measure.map π ν) := hfc.aestronglyMeasurable
  have hint : Integrable f (Measure.map π ν) := by
    rw [integrable_map_measure hfm hm.aemeasurable, hcomp]
    exact hi
  have hμ : μ = (c⁻¹ : NNReal) • Measure.map π ν := by
    rw [hmap, smul_smul, _root_.inv_mul_cancel₀ hc, one_smul]
  refine ⟨?_, ?_⟩
  · rw [hμ]
    exact hint.smul_measure_nnreal
  · rw [hμ, integral_smul_nnreal_measure, integral_map hm.aemeasurable hfm]
    simp only [hf, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]

theorem zetaLaw_of_cover : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (br : Bool) (e : Ix p q ≃ Fin W.rank) (e' : Ix r s ≃ Fin V.rank) (u : kfin N τ → (X.ds p q lam).HK.V) (K : ℝ), ARi X lam lam' → (∀ v, UnitHW (X.ds p q lam) (blattner lam) v → Integrable (eFun (X.ds p q lam) v) (X.grp p q).haar) → KTie (X.ds p q lam) N τ lam c br false e u → SignCompat (M.ε τ) e' → (m : ℚ) = 2 * c → Coef (X.fock p q r s) B pt ip κ (phiFr (N.fr τ) br e) m K → (∀ Φ, IsJoint M τ A pt N B Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') (κ Φ)) → ZetaLaw M τ A pt N B ip := by
  intro D V S M W S' N τ ι Z A B pt ip X p q r s lam lam' κ c m br e e' u K hA hI hT hS hm hC hJ
  intro Φ hΦ v hv μ hμ
  obtain ⟨hsc, -, -⟩ := hT.ord
  obtain ⟨π, c0, hc0, humat, hq, hπm, hmap⟩ :=
    GlobalTheory.T.cover_haar_pushforward_signatureUnitaryGroup p q W.rank (X.grp p q) (N.ε τ) e br μ hsc hμ
  have huv : UnitHW (X.ds p q lam) (blattner lam) (u v) := (hT.hi v).1 hv
  have huv1 : ‖(X.ds p q lam).ι (u v)‖ = 1 := by
    obtain ⟨-, h⟩ := huv
    exact h
  have hv1 : ‖(v : N.H τ)‖ = 1 := by
    obtain ⟨h, -⟩ := hv
    exact h
  obtain ⟨hK, hC1, hC2⟩ := hC
  obtain ⟨-, hA2⟩ := hA
  obtain ⟨c', hc', hJHW⟩ :=
    (GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness X p q r s (blattner lam) (blattner lam')).2.1 (κ Φ) (hJ Φ hΦ)
  obtain ⟨hIntC, hEqC, hPosC, hCpt⟩ := hA2 _ (u v) hJHW huv

  have hFc : ∀ x, Continuous fun g : (X.grp p q).G => (X.fock p q r s).π (g, 1) x := by
    intro x
    have h1 := (X.fock p q r s).7 x
    have h2 := GlobalTheory.FockEmbExp.continuous_emb (X.fock p q r s)
    have h3 : Continuous fun g : (X.grp p q).G => ((g, 1) : (X.grp p q).G × (X.grp r s).G) := by fun_prop
    exact h1.comp (h2.comp h3)
  have hmc : Continuous fun g => mcoef (X.ds p q lam) (u v) g := by
    show Continuous fun g => ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ
    exact continuous_const.inner ((X.ds p q lam).U.cont _)
  have hsqc : Continuous fun g : (X.grp p q).G => (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m :=
    (GlobalTheory.RealPar.Cover.continuous_sq (T := X.grp p q)).zpow₀ m fun g => Or.inl (X.grp p q |>.sq g).ne_zero
  have hsq : ∀ g : (X.grp p q).G,
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * star ((((X.grp p q).sq g : ℂˣ) : ℂ) ^ m) = 1 := by
    intro g
    have h1 := GlobalTheory.RealPar.Cover.norm_sq (T := X.grp p q) g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, _root_.norm_zpow, h1, _root_.one_zpow]
    norm_num

  have hcoef : ∀ g, ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ =
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := by
    intro g
    rw [humat g]
    exact hT.coef m hm g v v

  have hip : ∀ g, ip (B ((N.fr τ)⁻¹ * umat (π g) * N.fr τ) (pt Φ)) (pt Φ) =
      (K : ℂ) * (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m *
        ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ := by
    intro g
    rw [humat g]
    exact hC2 g Φ Φ
  have hscal : ∀ g, ⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
      (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ =
      (c' : ℂ) ^ 2 * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ := by
    intro g
    rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  have hc2 : ((c' : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hc'.ne')
  have hc2' : ((c' : ℂ) ^ 2)⁻¹ * (c' : ℂ) ^ 2 = 1 := _root_.inv_mul_cancel₀ hc2

  have hkc : Continuous fun g : (X.grp p q).G => (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) :=
    continuous_const.mul ((continuous_const.inner (hFc _)).mul hmc.star)
  have hki : Integrable (fun g : (X.grp p q).G => (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g))) (X.grp p q).haar :=
    hIntC.const_mul _
  have hfk : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) => ip (B (ofFr N τ (umat g')) (pt Φ)) (pt Φ) *
      star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) (π g) =
      (K : ℂ) * ((c' : ℂ) ^ 2)⁻¹ *
      (⟪(X.fock p q r s).ι ((c' : ℂ) • κ Φ),
        (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) := by
    intro g
    show ip (B ((N.fr τ)⁻¹ * umat (π g) * N.fr τ) (pt Φ)) (pt Φ) *
      star ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ = _
    rw [hip g, hcoef g, hscal g, _root_.star_mul']
    linear_combination
      ((K : ℂ) * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).π (g, 1) ((X.fock p q r s).ι (κ Φ))⟫_ℂ *
        star (mcoef (X.ds p q lam) (u v) g)) * (hsq g - hc2')
  obtain ⟨hfi, hfe⟩ := transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => ip (B (ofFr N τ (umat g')) (pt Φ)) (pt Φ) *
      star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g'))) hc0 hq hπm hmap hkc hfk hki
  rw [integral_const_mul, hEqC] at hfe

  have hk1c : Continuous fun g : (X.grp p q).G =>
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := hsqc.mul hmc
  have hfd : ((X.ds p q lam).fdeg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (X.ds p q lam).fdeg_pos.ne'
  have hk1i : Integrable (fun g : (X.grp p q).G =>
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g) (X.grp p q).haar := by
    refine ((hI (u v) huv).const_mul ((X.ds p q lam).fdeg : ℂ)⁻¹).mono hk1c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => le_of_eq ?_)
    show _ = ‖((X.ds p q lam).fdeg : ℂ)⁻¹ * (((X.ds p q lam).fdeg : ℂ) * star (mcoef (X.ds p q lam) (u v) g))‖
    rw [← mul_assoc, _root_.inv_mul_cancel₀ hfd, one_mul, norm_star, _root_.norm_mul, _root_.norm_zpow,
      GlobalTheory.RealPar.Cover.norm_sq, _root_.one_zpow, one_mul]
  have hk1f : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) =>
      Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g') (π g) =
      (((X.grp p q).sq g : ℂˣ) : ℂ) ^ m * mcoef (X.ds p q lam) (u v) g := hcoef
  refine ⟨(transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) hc0 hq hπm hmap hk1c hk1f hk1i).1, hfi, ?_, ?_⟩
  · refine ⟨(c0 : ℝ)⁻¹ * ((K : ℝ) * (c' ^ 2)⁻¹ *
      (‖opE (X.grp p q) (fun g => (X.fock p q r s).π (g, 1)) (eFun (X.ds p q lam) (u v))
          ((X.fock p q r s).ι ((c' : ℂ) • κ Φ))‖ ^ 2 / (X.ds p q lam).fdeg)), ?_, ?_⟩
    · have h0 : (0 : ℝ) < c0 := lt_of_le_of_ne c0.2 (fun h => hc0 (NNReal.coe_eq_zero.mp h.symm))
      have h1 := (X.ds p q lam).fdeg_pos
      positivity
    · rw [hfe]
      push_cast
      ring
  · intro hall d hd
    have hs0 : r = 0 ∨ s = 0 := by
      right
      by_contra hs
      have h := hS (Sum.inr ⟨0, Nat.pos_of_ne_zero hs⟩)
      rw [hall] at h
      simp at h
    obtain ⟨hopE, hEq1⟩ := hCpt hs0
    rw [hopE] at hEqC

    have hn : ‖(X.fock p q r s).ι ((c' : ℂ) • κ Φ)‖ ^ 2 = 1 := by
      have h := hEqC.symm.trans hEq1
      have h' : ‖(X.fock p q r s).ι ((c' : ℂ) • κ Φ)‖ ^ 2 / (X.ds p q lam).fdeg =
          ((X.ds p q lam).fdeg)⁻¹ := by exact_mod_cast h
      have hfd' := (X.ds p q lam).fdeg_pos
      field_simp at h'
      linarith
    have hn' : (c' : ℂ) ^ 2 * ⟪(X.fock p q r s).ι (κ Φ), (X.fock p q r s).ι (κ Φ)⟫_ℂ = 1 := by
      rw [map_smul, _root_.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc', _root_.mul_pow] at hn
      rw [inner_self_eq_norm_sq_to_K]
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) hn
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one] at h2
      exact h2

    obtain ⟨hd0, hd1⟩ := hd
    have hsch := (X.ds p q lam).schur ((X.ds p q lam).ι (u v)) ((X.ds p q lam).ι (u v))
    have hk2c : Continuous fun g : (X.grp p q).G =>
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_const.inner ((X.ds p q lam).U.cont _)).norm.pow 2)
    have hk2i : Integrable (fun g : (X.grp p q).G =>
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
        (X.grp p q).haar := hsch.1.ofReal
    have hk2f : ∀ g, (fun g' : Formalism.REAL.UJ (N.ε τ) =>
        Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g' *
          star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g')) (π g) =
        ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      show ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ * star ⟪(v : N.H τ), N.σ τ (umat (π g)) v⟫_ℂ = _
      rw [hcoef g, _root_.star_mul']
      have hm2 : mcoef (X.ds p q lam) (u v) g * star (mcoef (X.ds p q lam) (u v) g) =
          ((‖⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
        show ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ *
          star ⟪(X.ds p q lam).ι (u v), (X.ds p q lam).U.π g ((X.ds p q lam).ι (u v))⟫_ℂ = _
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      linear_combination (mcoef (X.ds p q lam) (u v) g * star (mcoef (X.ds p q lam) (u v) g)) * hsq g + hm2
    have hfd2 := (transfer (f := (fun g' : Formalism.REAL.UJ (N.ε τ) => Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g' *
          star (Formalism.MainNotions.S.coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v g'))) hc0 hq hπm hmap hk2c hk2f hk2i).2
    beta_reduce at hfd2
    rw [integral_complex_ofReal, hsch.2, huv1, (hd1 v v v v).2, inner_self_eq_norm_sq_to_K, hv1] at hfd2
    rw [hfe, hopE, hn, hC1 Φ Φ, eq_inv_of_mul_eq_one_right hn']
    have hd0' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd0.ne'
    have hc0' : ((c0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hc0)
    push_cast at hfd2 ⊢
    linear_combination (-(K : ℂ) * ((c' : ℂ) ^ 2)⁻¹) * hfd2

end GlobalTheory.ArchRec.ZetaTransfer
