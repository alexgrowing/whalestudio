import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
private lemma opApply_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (c : ℂ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply Θ (c • F) g = c • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  simp only [_root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, Pi.smul_apply, map_smul]
  rw [List.smul_sum, List.map_map]
  rfl

open Filter Topology MeasureTheory in
private lemma vecV_smul_jet_harmonics {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν : Fin (2 * r + k + 1) → ℂ) (m : _root_.Formalism.FourierDecayAlt.B.Mat k r) (c : ℂ)
    (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m (fun g => c • G g) q = c • _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m G q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · apply _root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
    refine MeasureTheory.ae_of_all _ fun x => ?_
    unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact smul_comm _ _ _
  · simp
  · simp

open Filter Topology MeasureTheory in
private lemma topLift_vecV_add_smul_lemma {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : _root_.Formalism.FourierDecayAlt.M.Par} (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    {Cb : ℝ} (a : ℂ) {H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List _root_.Formalism.FourierDecayAlt.C.Letter}
    (hdom : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hcut : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (h₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂) (i : _root_.Formalism.FourierDecayAlt.Wd.Ix (Fin w.length))
    (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    p.V (p.Θ.Θ w i (H₁ + a • H₂)) q = p.V (p.Θ.Θ w i H₁) q + a • p.V (p.Θ.Θ w i H₂) q := by
  obtain ⟨nf, fib, o, κ, D, -, hD, -, -, hΘ⟩ := hdom w hcut i
  have hlen : ∀ T ∈ D, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, es, -, -, hl, -⟩ := hD.2.2 T hT
    omega
  have hpos : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GPos p.T.base, g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, by simp⟩
  have hc₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₁ hD.1
  have hc₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₂ hD.1
  have e₁ : p.V (p.Θ.Θ w i H₁) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₁ g (hpos g hg)
  have e₂ : p.V (p.Θ.Θ w i H₂) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₂ g (hpos g hg)
  have e₃ : p.V (p.Θ.Θ w i (H₁ + a • H₂)) q =
      p.V (fun g => _root_.Formalism.FourierDecayAlt.B.opApply D H₁ g - (fun g => (-a) • _root_.Formalism.FourierDecayAlt.B.opApply D H₂ g) g) q := by
    refine _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
    have hsum : H₁ + a • H₂ = H₁ - (-a) • H₂ := by rw [neg_smul, sub_neg_eq_add]
    rw [hΘ _ g (hpos g hg), hsum,
      _root_.Formalism.FourierDecayAlt.P.PBE.opApply_subGV D hlen (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₁.1 o) (_root_.Formalism.FourierDecayAlt.P.B4.ckOn_smul (-a) (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₂.1 o)) g hg.1, opApply_smul]
  have e₄ := _root_.Formalism.FourierDecayAlt.P.PBN.vecV_sub p.T.base p.ν' p.m₀ q hc₁ (_root_.Formalism.FourierDecayAlt.P.PBN.cpt_smul p.T.base (-a) hc₂)
  have e₅ := vecV_smul_jet_harmonics p.T.base p.ν' p.m₀ (-a) (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q
  rw [e₁, e₂, e₃]
  change _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q = _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q + a • _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q
  rw [e₄, e₅, neg_smul, sub_neg_eq_add]

open Filter Topology MeasureTheory in
private lemma hsVec_add_jet_harmonics {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (A B : Wq →L[ℂ] Wp) : _root_.Formalism.FourierDecayAlt.B.hsVec (A + B) = _root_.Formalism.FourierDecayAlt.B.hsVec A + _root_.Formalism.FourierDecayAlt.B.hsVec B := by
  unfold _root_.Formalism.FourierDecayAlt.B.hsVec
  rfl

open Filter Topology MeasureTheory in

theorem _root_.GlobalTheory.TopVec.tv_add_smul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (c : Fin (P.r + 1) → ℂ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂ → _root_.GlobalTheory.TopVec.tv p (H₁ + a • H₂) w c = _root_.GlobalTheory.TopVec.tv p H₁ w c + a • _root_.GlobalTheory.TopVec.tv p H₂ w c := by
  intro Wp Wq _ _ _ _ _ _ P p Cb a H₁ H₂ w c hdom hcut h₁ h₂
  unfold _root_.GlobalTheory.TopVec.tv
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext x
  rw [topLift_vecV_add_smul_lemma p a hdom hcut h₁ h₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, hsVec_add_jet_harmonics, _root_.Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, smul_add, Pi.add_apply, Pi.smul_apply,
    smul_comm a]

end GlobalTheory.TopVec
