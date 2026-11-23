import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def SiteOpsWaveJC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (j : Fin 6), (j = 1 ∨ j = 4) →
    ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → X.op l j Φ ∈ waveJ P z z' π π' D l

namespace SiteC

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (ι : B.Mat k r → ℂ)
    (hι : ∀ p : B.SS k r, Bs.inSS p → ∀ g, ι (B.sgs p g) = ι g) (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => ι g • G g) h = ι h • B.JF Bs G h := by
  unfold B.JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [B7.ae_inSS Bs] with p hp
  have hp' := hι p hp h
  simp only [B.sgs] at hp'
  simp only [hp', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm (ι h)]

theorem first_minor_double_coset_invariant (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (hp : Bs.inSS p) (g : B.Mat k r) :
    Dmin k r Bs.z Bs.z' (B.sgs p g) ⟨1, by omega⟩ = Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩ :=
  Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _

private theorem dmin_one_eq_herm_mulVec_fvec {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Dmin k r z z' g ⟨1, by omega⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  erw [Matrix.det_fin_one]
  rfl

theorem first_minor_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩) := by
  refine JCx2.mn_good_congr (c := fun g => herm (Hpk k r) (g *ᵥ fvec k r Bs.z' 0) (fvec k r Bs.z 0)) ?_
    (JCx2.mn_good_herm _ _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]

theorem first_minor_conj_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => star (Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩)) := by
  refine JCx2.mn_good_congr
    (c := fun g => (Complex.conjCLE.toContinuousLinearMap.comp
      (JCx2.mnLinHerm (k := k) (r := r) (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) g) ?_
    (JCx2.mn_good_lin _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]
  simp [JCx2.mnLinHerm]

private theorem wCell_succ_mulVec_bvec_eI_zero_eq_smul {k r : ℕ} (hr : 0 < r) (c : Fin r → ℂ) :
    ∀ (i : ℕ) (hi : i < r), wCell k r ⟨i + 1, by omega⟩ c *ᵥ bvec (eI k r ⟨0, hr⟩) =
      c ⟨0, hr⟩ • bvec (esI k r ⟨0, hr⟩) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨0, hr⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.mk_zero, Qx6.wCell_zero, one_mul] at h
    rw [h, Qx4.w1_mulVec_bvec_eI]
  | succ n ih =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨n + 1, hi⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h
    have h1 : eI k r ⟨0, hr⟩ ≠ eI k r ⟨n + 1, hi⟩ := by
      simp [eI, Fin.ext_iff]
    have h2 : eI k r ⟨0, hr⟩ ≠ esI k r ⟨n + 1, hi⟩ := by
      simp [eI, esI, Fin.ext_iff]; omega
    rw [h, ← Matrix.mulVec_mulVec, Qx3.reflection_fixes_basis_vector _ _ h1 h2, ih (by omega)]

theorem first_minor_at_cell_eq_coefficient {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, by omega⟩ = c ⟨0, hr⟩ := by
  rw [dmin_one_eq_herm_mulVec_fvec]
  have hf : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w 0 = bvec (eI k r ⟨0, hr⟩) := by
    intro w; simp [fvec, hr]
  rw [hf, hf, ← Matrix.mulVec_mulVec, (hg.2 ⟨0, hr⟩ (by simp; omega)).1]
  have h3 := wCell_succ_mulVec_bvec_eI_zero_eq_smul (k := k) hr c (r - 1) (by omega)
  have e : (⟨r - 1 + 1, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; simp; omega
  rw [e] at h3
  rw [h3]
  simp only [herm, bvec, eI, esI]
  simp
  rw [Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one]
  simp [Hpk, hr]

end SiteC

open SiteC in
theorem site_operators_preserve_orbital : SiteOpsWaveJC := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D _ _ _ hz hz' hπ hπ' l hl j hj Φ hΦ
  subst hz hz' hπ hπ'
  have hr : 0 < P.r := by have := l.2; omega
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have key : ∀ Ψ, IsWaveJ P D.z D.z' D.π D.π' D l Ψ → IsWaveJ P D.z D.z' D.π D.π' D l (X.op l j Ψ) := by
    rintro Ψ ⟨hlc, s, ε, G, hε, hG, hΨ⟩
    rcases hj with rfl | rfl
    · refine ⟨?_, s, ε, fun g => Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩ • G g, hε, first_minor_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => BigCellZetaMinors.dmin_sgs D hp g _) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
    · refine ⟨?_, s, ε, fun g => star (Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩) • G g, hε, first_minor_conj_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cbOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cbOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => by rw [BigCellZetaMinors.dmin_sgs D hp g _]) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
  refine Submodule.span_induction (p := fun Φ _ => X.op l j Φ ∈ waveJ P D.z D.z' D.π D.π' D l) ?_ ?_ ?_ ?_ hΦ
  · intro x hx
    exact Submodule.subset_span (key x hx)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem site_multiplication_orbital : SiteMulWaveJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl Φ hΦ
  exact ⟨site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 1 (Or.inl rfl) Φ hΦ,
    site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 4 (Or.inr rfl) Φ hΦ⟩

end Formalism.FourierDecayAlt.P.CutSE
