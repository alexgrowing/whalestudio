import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Formalism.LocalToGlobal.ProjectiveLattices.CurveCountB

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem formsEvR_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPlus h j hj).inc u F) = evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j) :=
  formsEvR_single j hG hT Z _ _

theorem birAt_of_ev {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : PJ D B P j) (N : ℕ) {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (ev : ∀ u : WeightFamilies.Wt D j, B.Cusp j u → Ω) (hev : ∀ u F, gF (X.inc u F) = ev u F)
    (hB : ∀ a : Ω, ∃ (k : ℕ) (g : B.Cusp j (wsmul k wL)) (Pw : MvPolynomial (Fin N) B.KO), Pw.IsHomogeneous k ∧
      MvPolynomial.aeval (fun i => ev wL (w i)) Pw ≠ 0 ∧
      a * MvPolynomial.aeval (fun i => ev wL (w i)) Pw = ev (wsmul k wL) g) :
    CurveLoc.BirAt X N w gF := by
  intro a
  obtain ⟨k, g, Pw, hP, hne, he⟩ := hB a
  refine ⟨k, g, Pw, hP, ?_, ?_⟩
  · simp only [hev]
    exact hne
  · simp only [hev]
    exact he

theorem birAt_of {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BIRSt h j hj hG G)
    (Z : Comp (T.Q.Xo j) T.Q.c) : CurveLoc.BirAt (recPlus h j hj) G.N G.w (formsEvR j hG hT Z) :=
  birAt_of_ev j (recPlus h j hj) G.N G.w (formsEvR j hG hT Z)
    (fun u F => evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j))
    (fun u F => formsEvR_inc h j hj hG hT Z u F) (hB Z)

theorem split_of (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (Z : Comp (T.Q.Xo j) T.Q.c) (k : Fin G.N) :
    ∃ g : (recB h.toLawsCore).Cusp j wL,
      formsEvR j hG hT Z ((recPlus h j hj).inc wL g) = formsEvR j hG hT Z ((recPlus h j hj).inc wL (G.w k)) ∧
      ∀ Z', Z' ≠ Z → formsEvR j hG hT Z' ((recPlus h j hj).inc wL g) = 0 := by
  obtain ⟨g', h1, h2⟩ := hC Z wL (G.w k)
  exact ⟨g', by rw [formsEvR_inc, formsEvR_inc, h1], fun Z' hZ' => by rw [formsEvR_inc, h2 Z' hZ']⟩

def CountQAtSt : Prop :=
  ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)),
    CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      CurveLoc.CountQAt (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)

theorem hone_of (hC : CompSplitSt h j hG) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z' := by
  intro ka wL wF G S g0 la _ Q hQ _ Z Z' hZ hZ'
  exact CurveLoc.one_of_split (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun Z k => split_of h j hj hG hT hC G Z k) Q hQ Z Z' hZ hZ'

theorem hloc_of (hB : ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
      (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → BIRSt h j hj hG G)
    (hQ : CountQAtSt h j hj hG hT) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
  intro ka wL wF G S g0 la hH Z r
  exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (birAt_of h j hj hG hT G (hB ka wL wF G S g0 hH) Z) (hQ ka wL wF G S g0 la hH Z) r

theorem countQAtSt_holds : CountQAtSt h j hj hG hT := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨k₀, hk₀, htr⟩ := hH.2.1.2 Z
  exact CurveLoc.countQAt_of (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun i => formsEvR_inc h j hj hG hT Z wL (G.w i)) ⟨k₀, hk₀, le_of_eq htr⟩

theorem hloc_of_bir (hB : ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
      (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → BIRSt h j hj hG G) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a :=
  hloc_of h j hj hG hT hB (countQAtSt_holds h j hj hG hT)

end Formalism.L2.Pj
