import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic GlobalTheory.UU

noncomputable def tqOfIso {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (T : TQ G X) {A : Over S}
    [GrpObj A] (hA : IsAbelianScheme A) (β : T.B ≅ A) [IsMonHom β.hom] : TQ G X :=
  haveI : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  { B := A
    comm := hA.comm
    isAb := hA
    q := T.q ≫ β.hom
    i := T.i
    q_hom := by have := T.q_hom; infer_instance
    i_hom := T.i_hom
    q_flat := by have := T.q_flat; rw [Over.comp_left]; infer_instance
    q_surj := by have := T.q_surj; rw [Over.comp_left]; infer_instance
    q_affine := by have := T.q_affine; rw [Over.comp_left]; infer_instance
    isKernel := by
      have sq : IsPullback η[T.B] (𝟙 _) β.hom η[A] :=
        IsPullback.of_vert_isIso ⟨by rw [IsMonHom.one_hom, Category.id_comp]⟩
      have h := T.isKernel.paste_vert sq
      rwa [Category.comp_id] at h
    loc := fun b χ => by
      obtain ⟨V, hV, u, hu⟩ := T.loc (β.inv.left b) χ
      have le : (T.q ≫ β.hom).left ⁻¹ᵁ (β.inv.left ⁻¹ᵁ V) ≤ T.q.left ⁻¹ᵁ V := by
        rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, Category.assoc, β.hom_inv_id, Category.comp_id]
      exact ⟨β.inv.left ⁻¹ᵁ V, hV, res le u, hu.res le⟩ }

theorem lamdiff : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (N : LB T.B.left), N.IsLB → ∀ t : LB.Gen (N.pull T.q.left), t.IsGen → ∃ (χ : X) (t' : LB.Gen (N.pull T.q.left)), T.GenWt N t' χ) → ∀ (Q : Out.PolAV (Sp ℂ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (β : T.B ≅ Q.A), IsMonHom β.hom → ∀ M : LB Q.A.left, M.IsLB → LBIso (M.pull (T.q ≫ β.hom).left) (Q.L.pull (T.q ≫ β.hom).left) → ∃ u : LB.Gen (abelian₂ Q.A (LB.div M Q.L)), u.IsGen := by
  intro hw Q X _ _ _ G _ _ T β hβ M hM hiso
  haveI := hβ
  have hL := Q.isLB
  have hN : (LB.div M Q.L).IsLB := LB.isLB_div hM hL
  have hNp : ((LB.div M Q.L).pull (T.q ≫ β.hom).left).IsLB := LB.isLB_pull hN _
  have hc : cls ((LB.div M Q.L).pull (T.q ≫ β.hom).left) hNp = 0 := by
    rw [cls_pull hN _ hNp, cls_div hM hL hN, map_sub,
      ← cls_pull hM _ (LB.isLB_pull hM _), ← cls_pull hL _ (LB.isLB_pull hL _), sub_eq_zero]
    exact (cls_eq_iff _ _).2 hiso
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff hNp).1 hc
  let T' := tqOfIso T Q.isAb β
  obtain ⟨χ, t', ht'⟩ := hw ℂ X G T' (LB.div M Q.L) hN t ht
  obtain ⟨N', s, hN', hs, u, hu⟩ := GlobalTheory.WtBundle.exists_genWt T' χ
  have hI : LBIso (LB.div M Q.L) N' := GlobalTheory.UU.lbIso_of_genWt _ X G T' _ N' t' s χ hN hN' ht' hs
  have hLam : (abelian₂ Q.A (LB.div M Q.L)).IsLB := LB.isLB_linComb hN _ _
  have hLam' : (abelian₂ Q.A N').IsLB := LB.isLB_linComb hN' _ _
  have h0 := (cls_eq_zero_iff hLam').2 ⟨u, hu⟩
  refine (cls_eq_zero_iff hLam).1 ?_
  refine (cls_linComb hN _ _ hLam).trans ?_
  rw [(cls_eq_iff hN hN').2 hI]
  exact (cls_linComb hN' _ _ hLam').symm.trans h0

end PositivityTheory.HtPt.Ppic
