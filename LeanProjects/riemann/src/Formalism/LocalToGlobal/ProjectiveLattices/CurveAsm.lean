import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

set_option maxHeartbeats 1000000 in

abbrev phiI (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (Z : Comp (T.Q.Xo j) T.Q.c) :=
  phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w

def CurveHyp (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  SpanW (recPlus h j hj) G.w S ∧ BigAt h j hj hG G ∧ ThAt h j hj hG G g0 ∧ (recPlus h j hj).NonZeroComp wF g0

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in

theorem curveInst_of [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    (hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0)
    (hone : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z')
    (hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a)
    (hS1 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)))
    (hH2 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL),
        (∀ Z, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) →
        IsUnit (toOsK (recPlus h j hj) la G.w (u0 (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 θ hw)))
    (hH3 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
        (b : Lw (recPlus h j hj) la G.w) *
          algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
            (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 → b = 0) :
    CurveInstSt h j hj := by
  intro _ ka wL wF G la S g0 hSp hBig hTh hNZ
  have hH : CurveHyp h j hj hG ka wL wF G S g0 := ⟨hSp, hBig, hTh, hNZ⟩
  have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w) (Jid (recPlus h j hj) la G.w)
    (Comp (T.Q.Xo j) T.Q.c) (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
    (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
    (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
  obtain ⟨e, w', θ, hw, hθ⟩ := hTh
  exact curveModel_of_fr (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 h1.1 h1.2 θ hw
    (hH2 _ _ _ G S g0 la hH e w' θ hw hθ) (hH3 _ _ _ G S g0 la hH)

end Formalism.L2.Pj
