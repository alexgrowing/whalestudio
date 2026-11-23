import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousZetaL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HerGenC

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem hsInner_zero_left' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_zero_small (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {G : B.Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g)
    (q : C.LPt) (hq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q < ε) : D.vecV Bs ν' m₀ G q = 0 := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) G (fun _ => 0) 0 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        have hz : G (B.sgs p h'.choose) = 0 := by
          by_contra hne
          have h1 := hG _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hne
          rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, ← hGq] at h1
          linarith
        simp [D.orbIntegrand, B.rho, hz])
      rw [e, zero_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

theorem rr_top_small {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℂ, Complex.normSq c - P.T * P.T' < δ →
      p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
  classical

  have hθc := fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hθ hF hw
  choose F' hF'c hF'd hF'v using hθc
  obtain ⟨εF, hεF, hGF⟩ := hF.2.2
  choose εe hεe hGe using fun e => (hF'c e).2.2
  let Sε : Finset ℝ := insert εF (Finset.univ.image εe)
  have hne : Sε.Nonempty := ⟨εF, Finset.mem_insert_self _ _⟩
  set ε := Sε.min' hne with hεdef
  have hε : 0 < ε := by
    rw [hεdef, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hεF
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεe a
  have hεF' : ε ≤ εF := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hεe' : ∀ e, ε ≤ εe e := fun e =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ e)))
  set Dh := Complex.normSq (D.ptMatN h P.r).det with hDh
  have hD0 : 0 ≤ Dh := Complex.normSq_nonneg _
  have hD1 : 0 < Dh + 1 := by linarith
  refine ⟨ε / (Dh + 1), div_pos hε hD1, fun c hc => ?_⟩
  have hTT : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' = P.T * P.T' := by
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  have hpt : D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (h ++ [(1, c)]) < ε := by
    rw [hTT, Formalism.FourierDecayAlt.P.PBD.ptG_app _ c h P.r hh.2]
    by_cases hs : Complex.normSq c - P.T * P.T' ≤ 0
    · have : Dh * (Complex.normSq c - P.T * P.T') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD0 hs
      linarith
    · push Not at hs
      have h1 : Dh * (Complex.normSq c - P.T * P.T') ≤ (Dh + 1) * (Complex.normSq c - P.T * P.T') := by nlinarith
      have h2 : (Dh + 1) * (Complex.normSq c - P.T * P.T') < (Dh + 1) * (ε / (Dh + 1)) :=
        mul_lt_mul_of_pos_left hc hD1
      rw [mul_div_cancel₀ _ hD1.ne'] at h2
      linarith
  unfold KB.Pl.RR D.RRplace
  split_ifs with hloc hi hi2 hw0
  · omega
  · have hv : D.vecV p.T.base p.ν' p.m₀ F (h ++ [(1, c)]) = 0 :=
      vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans hεF' (hGF g hg h0)) _ hpt
    rw [hv, hsInner_zero_left']
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    have hv : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(1, c)]) = 0 := by
      have := hF'v e (h ++ [(1, c)])
      unfold KB.Pl.V at this
      rw [this]
      exact vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans (hεe' e) (hGe e g hg h0)) _ hpt
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left', mul_zero]
  · omega
  · rfl

section law

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zetaNorm_map {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ) :
    μ.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      (volume : Measure ℂ).withDensity (Formalism.FourierDecayAlt.P.JCx2.rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ hf, hμ.2 ψ hψ, lintegral_withDensity_eq_lintegral_mul _ (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _) hψ]
  rfl

theorem zetaNorm_integral {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ) :
    ∫ g, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) ∂μ =
      ∫ ζ, (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  rw [← integral_map hf.aemeasurable hψ.aestronglyMeasurable, zetaNorm_map hμ,
    integral_withDensity_eq_integral_toReal_smul (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
      (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

theorem zetaNorm_integrable {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ)
    (hi : Integrable (fun g => ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g))) μ) :
    Integrable (fun ζ => (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  have h1 : Integrable ψ (μ.map fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) :=
    (integrable_map_measure hψ.aestronglyMeasurable hf.aemeasurable).2 hi
  rw [zetaNorm_map hμ, integrable_withDensity_iff_integrable_smul' (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
    (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

end law

section pic

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pic_cpt {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (K0 : Submodule ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π'))
    (hJ : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
        (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
      (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2 := by
  classical
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  set F₂ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => if g ∈ B.GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ B.GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hs₂ : B.CkOn ⊤ (B.GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun g hg hgG => by rw [he g hgG, hfe g hg hgG]⟩
  have hz : ∀ g, g ∉ {g : B.Mat k r | B.gN g ≤ R} → F₂ g = 0 := by
    intro g hg
    by_cases hgG : g ∈ B.GV k r
    · rw [he g hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · simp [hF₂, hgG]
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  obtain ⟨Φ, hΦK, hΦ⟩ := hJ F₂ ε hε
    (fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs₂ hC (fun g _ hgC => hz g hgC) A m)
    (HasCompactSupport.intro hC hz)
    (fun g hg h0 => hG g hg (by rwa [he g hg] at h0))
  refine ⟨Φ, hΦK, fun x hx => ?_⟩
  rw [hΦ x hx]
  have hGV : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hx.1 (by simp)) hx.2.1.1
  simp only [resG]
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (a := 1) (fun g hg => by rw [he g hg, one_smul]) hGV, one_smul]

end pic

def TopContOn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F →
    KB.CutWord P p.l0 w →
    ContinuousOn (fun c : ℂ => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]))
      {c : ℂ | P.T * P.T' < Complex.normSq c}

end Formalism.FourierDecayAlt.P.PBO
