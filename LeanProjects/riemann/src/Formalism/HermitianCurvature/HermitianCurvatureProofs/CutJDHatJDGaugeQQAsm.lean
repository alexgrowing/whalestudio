import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAdm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBesselEigen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GaugeExistsQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

def JDecayTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

def JAdjTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JAdj (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem gaugeExistsQQ_of_gCore (hK : Gauge.GCore) : GaugeExistsQQ := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  exact jdg_exists_of_gCore hK 0 E Wp Wq S T f χ ν' m₀ top A₀ hB v

theorem modelPlaceBuilt3_of_leavesQQ (hMF : MA.ModelFrameAn) (h1 : LamCfgInterlaces) (h2 : AdmInCut)
    (h3 : GaugeExistsQQ) (h4 : RegFF3) (h5 : CVPresFF) (h6 : BesselEigen) (h7 : EnergyTr) (h8 : CutTr)
    (h9 : EnergyReal) (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : ModelPlaceBuilt3 := by
  obtain ⟨K3, g3⟩ := h3
  obtain ⟨K4, g4⟩ := h4
  obtain ⟨K5, g5⟩ := h5
  obtain ⟨K6, g6⟩ := h6
  obtain ⟨K7, g7⟩ := h7
  obtain ⟨K8, g8⟩ := h8
  obtain ⟨K9, g9⟩ := h9
  obtain ⟨K10, g10⟩ := h10
  obtain ⟨LastRowCutoff, g11⟩ := h11
  refine ⟨max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ hOk hW hW' c hc v
  have hOW : ∀ C', C' ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) →
      BuiltOW C' S T f χ ν' m₀ top A₀ := fun C' h => ⟨isBuiltPlace_mono h hB, hOk, hW, hW'⟩
  obtain ⟨_, _, _, hIB, hl1, hlk, hGr, hLC, _, _, hk2, _, hOn⟩ := hB
  obtain ⟨e, hF, hG, hQQ⟩ := g3 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K3 (by simp)) v
  have hR := g4 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K4 (by simp)) hJ v
  have hP := g5 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K5 (by simp)) v
  have hE := g6 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K6 (by simp)) v
  have hPOK : (D.parOf S v).OK := (hIB.2 v).2.2.2.1.1
  obtain ⟨L, hL, -⟩ := hMF (D.parOf S v) hPOK (S.l + 1) (by omega) (show S.l + 1 ≤ S.G.k by omega)
  have hI := h1 E Wp Wq S hk2 hOk hW hW' v
  have hlt : S.cutLo v < S.cutHi v := by
    have hv := hLC v
    have hN : (0 : ℝ) < S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; positivity
    have hX : 0 < (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    have h1le : (1 : ℝ) ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) :=
      le_max_left _ _
    nlinarith
  refine ⟨L, trJ S T v e (B.JF (T v).base (f v)), lamCfg S v, 1, 1, hc, one_pos, one_pos,
    ⟨hPOK, by omega, show S.l + 1 ≤ S.G.k by omega, hL, hI.1, hI.2, hlt, hOn v⟩,
    g10 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K10 (by simp)) v e L hF hG hQQ hL hR.1,
    g11 E Wp Wq S T f χ ν' m₀ top A₀ (hOW LastRowCutoff (by simp)) v e L hF hG hQQ hL hR.1, ?_, ?_, ?_⟩
  ·
    intro Y
    rw [← hG _ hR.1 Y, trJ_congr S T v e _ (((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v)) (hE Y), trJ_smul]
    funext π
    rw [Pi.smul_apply, ← prod_lamCfg S v Y]
    push_cast
    rfl
  ·
    intro ε hε a ha
    have key : C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
        MA.ipA (D.parOf S v)
          (MA.actA (D.parOf S v) ((a.reverse.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v))
            (S.l + 1)).QQ (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod)
            (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε))
          (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε) := by
      rw [g7 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K7 (by simp)) v e hF hP ε hε (hR.2 ε hε) a ha,
        (trJ_foldr S T v e hG hP a.reverse _ (hR.2 ε hε)).2,
        g8 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K8 (by simp)) v e hF hR.1 c hc ε hε]
    have hre := g9 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K9 (by simp)) v ε hε a ha
    rw [key] at hre
    rw [key]
    clear g3 g4 g5 g6 g7 g8 g9 g10 g11 hOW key hE hP hR hG hF hI hQQ
    unfold MA.cutoffEnergyForm
    simp only [one_mul]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact hre
  ·
    intro Lb a ha
    exact level_system_admissible_size S v a ha (h2 E Wp Wq S hGr v a ha) (S.l + 1) L _ c Lb

theorem modelPlaceBuilt3_of_openQQ (h3 : GaugeExistsQQ) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_leavesQQ Formalism.FourierDecayAlt.Final.ma_modelFrameAn eigenvalue_configuration_interlaces admissible_in_truncation_holds h3
    regularity_smooth_forms_holds coefficient_vector_preserves_form bessel_eigenvalue_equation_holds h7 cutoff_transport_to_model h9 h10 h11

theorem modelPlaceBuilt3_of_openGC (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_openQQ (gaugeExistsQQ_of_gCore hK) h7 h9 h10 h11

theorem modelPlaceBuilt2_of_openQQ (hJ : JfSmoothDS) (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal)
    (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3 hJ (modelPlaceBuilt3_of_openGC hK h7 h9 h10 h11)

end

end Formalism.FourierDecayAlt.P.CutMP
