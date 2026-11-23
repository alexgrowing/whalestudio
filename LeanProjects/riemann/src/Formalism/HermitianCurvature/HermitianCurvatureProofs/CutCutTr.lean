import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem cutTr_Gf_gq (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hc : ∀ a, q.1 a ≠ 0)
    (hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) :
    Formalism.QuantumDeterminants.Gf k r D.z D.z' (B.gq D q) =
      (∏ l, Complex.normSq (q.1 l)) * (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') := by
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
  have hPe : P = ∏ a : Fin r, q.1 a := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
    rw [this]
    congr 1
    ext a
    simp
  have hP0 : P ≠ 0 := by
    rw [hPe]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
    unfold zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  show Formalism.QuantumDeterminants.Gf k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) = _
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul, hPe, map_prod]
  ring

theorem cutTr_hsVec_contDiff [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    ContDiff ℝ ∞ (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  have h : (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) =
      ⇑((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ) := rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

theorem cutTr_jgq_smooth (D : B.RealPlaceData k r Wp Wq) (J : B.Mat k r → (Wq →L[ℂ] Wp)) (Om : Set (B.Mat k r))
    (hJ : Q.SmoothLev k r 0 Om J) (hOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ Om) :
    ContDiffOn ℝ ∞ (fun q => J (B.gq D q)) (JF.QDom k r D.z D.z') := by
  have hg : ContDiffOn ℝ ∞ (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D n
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ (B.gq D q) ⟨Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 hG.1, hOm q hq⟩
  refine ⟨JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ ∞ (F' ∘ fun q => B.gq D q)
      (JF.QDom k r D.z D.z' ∩ (JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1).1)

end helpers

theorem cutTr_normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 := by
    funext z; exact Complex.normSq_eq_norm_sq z
  rw [this]
  exact contDiff_norm_sq ℝ

theorem cutoff_transport_to_model : CutTr := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he hJ c hc ε hε
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF (T v).base (f v) (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => B.JF (T v).base (f v) (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  have hL : trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) ρ =
      MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) * u q) := by
    unfold trJ
    congr 1
    funext q
    rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, LE.Cut.sc, hc, pow_one, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e (B.JF (T v).base (f v)) ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dif_pos hu]
  rw [hL]
  show _ = MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) *
    (trJ S T v e (B.JF (T v).base (f v)) ρ).1 q)
  rw [hR]

end Formalism.FourierDecayAlt.P.CutMP
