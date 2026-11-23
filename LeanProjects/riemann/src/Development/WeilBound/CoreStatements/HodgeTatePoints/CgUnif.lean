import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _))).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul (a.trans b.symm))

theorem unif_pf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) := by
  intro E _ _ _ H R _ _ _ t P
  let I := IsLocalRing.maximalIdeal R
  let D := P.D.toPre
  let c := P.U.toUnifPre.gt 0
  let g : Sp (IsLocalRing.ResidueField R) ⟶ Sp (R ⧸ I ^ (0 + 1)) :=
    spMap (Ideal.Quotient.factor (show I ^ (0 + 1) ≤ I by simp))
  have hg : g ≫ Out.thick R I 0 = spMap (IsLocalRing.residue R) := by
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))
  obtain ⟨eG, mG, hG⟩ := grpPullback_iso (isGrpPullback_pullback t.G (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 t.G) g).comp (isGrpPullback_pullback t.G _)).congr hg rfl)
  obtain ⟨eB, mB, hB⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 D.P.A) g).comp (isGrpPullback_pullback D.P.A _)).congr hg rfl)
  obtain ⟨eT, mT, -⟩ := GlobalTheory.TorusExtBaseChange.exists_splitTorus_iso g (AddEquiv.refl D.X)
  have := c.q_hom
  have := c.i_hom
  obtain ⟨q, i, hq, hf, hs, ha, hi, hk, hqc, -⟩ := GlobalTheory.TorusExtBaseChange.exists_extension g eT eG eB c.i c.q
    c.q_flat c.q_surj c.q_affine c.isKernel
  have hM := pull_isLB D.P.isLB (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R)))
  refine ⟨{ X := D.X
            free := D.freeX
            finite := D.finX
            B := (Over.pullback (spMap (IsLocalRing.residue R))).obj D.P.A
            isAbelian := Out.TLinPf.isAb_pullback _ _ D.P.isAb
            q := q
            q_hom := hq
            q_flat := hf
            q_surjective := hs
            q_quasiCompact := inferInstance
            i := i
            i_hom := hi
            isKernel := hk }, D.P.L.pull (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R))), hM, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := lbIso_refl hM
    exact kTriv_pull (isGrpPullback_pullback D.P.A _) D.P.isLB hM ((isGen_iff w).1 hw) D.P.ktriv
  · have h0 : LBIso (P.U.toUnifPre.LG.L.pull (Out.fstG I 0 t.G).left) (D.P.L.pull c.pG.left) :=
      ⟨P.U.toUnifPre.w 0, P.U.toUnifPre.w_gen 0⟩
    rw [show P.U.toUnifPre.LG = t.PP from P.bundle] at h0
    refine h0.chartPull (h := eG.hom.left ≫ pullback.fst (Out.thickObj R I 0 t.G).hom g)
      (chartPullSame _ _ _ _ _ fun _ => ?_) (chartPullLinComb _ _ _ _ _ _ fun _ => ?_)
    · rw [Category.assoc]; exact hG.symm
    · show q.left ≫ _ = _ ≫ c.q.left ≫ pullback.fst D.P.A.hom (Out.thick R I 0)
      rw [← hB, ← Category.assoc _ c.q.left, ← hqc]
      simp only [Category.assoc]

end PositivityTheory.HtPt.Cg
