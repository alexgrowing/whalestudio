import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GenericSectionInjectiveOfAxH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FractionToIntegralSectionSmulEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDvdOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.SectionBasis

open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem basis_descends_record {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hB : InBasis G la)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) {Dd N : ℕ} (hD : Dd = WeightFamilies.dimY D j) (e : Fin G.N ≃ Fin (N + 1))
    (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin G.N → Ω Z) (hvF : ∀ Z k, gF Z (X.inc wL (G.w k)) = v Z k)
    (x : ∀ Z, Fin N → Ω Z) (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent B.KO (sImg (D := Dd) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N))
    (g0 : B.Cusp j wF) (θ : Fin G.del → ∀ Z, Ω Z) (hθ : ∀ k Z, gF Z (X.inc wF (G.th' k)) = θ k Z)
    (g : ∀ Z, Ω Z) (hgF : ∀ Z, gF Z (X.inc wF g0) = g Z) (hg : ∀ Z, g Z ≠ 0)
    (E : letI : ∀ Z, Module (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w ⧸
          Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)) := fun Z =>
        ((Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))).comp
          (algebraMap (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w))).toModule
      SectionSheafQuotient X la G.w wF ≃ₗ[Kp X la G.N] ∀ Z, RZs X la G.N (Ω Z) (gF Z) G.w ⧸
                           Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (hE : ∀ (F : B.Cusp j wF) Z, E (resF G la F) Z *
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)))) =
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F))))) :
    ∑ Z, Module.finrank (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N) = G.del ∧
    (∀ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) Dd N, ∃ q : MvPolynomial (TVar Dd N) B.KO, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z)) := by
  let iK : Algebra B.KO (Kp X la G.N) :=
    ((algebraMap (X.Kl la) (Kp X la G.N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la G.N) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨h1, h2⟩ := coords_of_equiv _ (tL G la) hB.1 hB.2 E
  refine basis_descends_loc (Kl := X.Kl la) hD e j0 v x hv hx hind hfin _ (GlobalTheory.CurveRecord.tv_indep X la G.N)
    (fun Z i => rzMap X la G.N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la G.w i))
    (fun Z i => by rw [GlobalTheory.CurveRecord.rzMap_sec_eq]; simp only [hvF])
    (fun Z => Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (fun Z => GlobalTheory.CurveRecord.map_Jid_eq X la G.N (Ω Z) (gF Z) G.w) _ (fun _ _ => rfl) θ g hg
    (fun k Z => E (tL G la k) Z) (fun k Z => ?_) h1 h2
  have := hE (G.th' k) Z
  rw [lwZ_alg, lwZ_alg, rzMap_emb, rzMap_emb, hgF, hθ] at this
  exact this

open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chosenForms_basis_of_value_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) {n : ℕ}
    (θ : Fin n → ∀ Z : Comp Xo c, Om Z) (g : ∀ Z : Comp Xo c, Om Z) (hg : ∀ Z, g Z ≠ 0) (eδ : Fin d.del ≃ Fin n)
    (h1 : ∀ p : Fin n → MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z) = 0) →
        ∀ k, p k = 0)
    (h2 : ∀ y : ∀ Z, OmS (Om Z) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, sHom (d.jc Z) (d.x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar d.D d.N) c.F, ∀ Z, sHom (d.jc Z) (d.x Z) q * y Z =
        ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z))
    (sel : Fin d.del → Fin d.np)
    (hsel : ∀ i Z, d.thp (sel i) Z = AddMonoidAlgebra.single d.wF (θ (eδ i) Z)) : A4Selection d sel := by
  refine ⟨fun Z => AddMonoidAlgebra.single d.wF (g Z), fun Z => ⟨mem_AG.2 ⟨_, rfl⟩, by simpa using hg Z⟩,
    fun p hp k => ?_, fun y => ?_⟩
  · have := h1 (fun k => p (eδ.symm k)) (fun Z => by
      rw [← hp Z, ← eδ.sum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsel, ratio_single _ _ _ (hg Z), eδ.symm_apply_apply]
      rfl) (eδ k)
    exact (congrArg p (eδ.symm_apply_apply k)).symm.trans this
  · obtain ⟨q, hq, p, hp⟩ := h2 y
    refine ⟨q, hq, fun k => p (eδ k), fun Z => (hp Z).trans ?_⟩
    rw [← eδ.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsel, ratio_single _ _ _ (hg Z)]
    rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chosenForms_restrict_basis_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → CurveHyp h j hj hG ka wL wF G S g0 → InBasis G la → ∃ eδ : Fin d.del ≃ Fin G.del, ∀ sel : Fin d.del → Fin d.np, (∀ i, d.thp (sel i) = valC hG (wtA wF) wF.n (G.th' (eδ i)).1) → d.wF = wtZ (wtA wF) wF.n → A4Selection d sel := by
  intro D T h j hj hG ka wL wF G S g0 la _ d e hD hw hb hH hB
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hA1 := independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G d e hD hw hb hH.2.1.2
  have hS := fun Z => GlobalTheory.genericSection_field (D := d.D) (d.jc Z) (d.x Z) (hfg Z) ((htr Z).trans (by rw [hD])) (hA1 Z)
  have hg := GlobalTheory.CurveRecord.evC_ne_zero h j hj hG hT (GlobalTheory.Reg.genValInj_record D T h j hj hG)
    (GlobalTheory.Reg.compSplit_record D T h j hj hG) G hH.2.1 g0 hH.2.2.2
  obtain ⟨⟨E, hE⟩, -⟩ := GlobalTheory.SectionProduct.tieS D T h j hj hG ka wL wF G hT S g0 la hH hB
  have hw' : ∀ i Z, d.w i Z = AddMonoidAlgebra.single (wtZ (wtA wL) wL.n) (evC hG Z (G.w (e.symm i)).1) := by
    intro i Z
    have := congrFun (hw (e.symm i)) Z
    rwa [e.apply_symm_apply] at this
  have hq : ∀ Z, evC hG Z (G.w (e.symm (d.jc Z))).1 ≠ 0 := by
    intro Z h0
    apply hb Z
    rw [hw', h0]
    simp
  have hx : ∀ Z k, d.x Z k =
      evC hG Z (G.w (e.symm ((d.jc Z).succAbove k))).1 / evC hG Z (G.w (e.symm (d.jc Z))).1 := by
    intro Z k
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hw', hw']
    exact ratio_single _ _ _ (hq Z)
  obtain ⟨h0, h1, h2⟩ := basis_descends_record (recPlus h j hj) la G hB (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) hD e d.jc (fun Z k => evC hG Z (G.w k).1)
    (fun Z k => formsEvR_inc h j hj hG hT Z wL (G.w k)) d.x hq hx (fun Z => (hS Z).1) (fun Z => (hS Z).2.1) g0
    (fun k Z => evC hG Z (G.th' k).1) (fun k Z => formsEvR_inc h j hj hG hT Z wF (G.th' k))
    (fun Z => evC hG Z g0.1) (fun Z => formsEvR_inc h j hj hG hT Z wF g0) hg E hE
  have hdel : d.del = G.del := h0
  refine ⟨finCongr hdel, fun sel hsel hF => ?_⟩
  exact chosenForms_basis_of_value_basis d (fun k Z => evC hG Z (G.th' k).1) (fun Z => evC hG Z g0.1) hg (finCongr hdel) h1 h2 sel
    (fun i Z => by rw [hsel, hF]; rfl)

end GlobalTheory.SectionBasis
