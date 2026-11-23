import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLiftOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PolIsoLift

theorem pol_iso : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  intro p _ D R _ b N k _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he hφ φ₂ hsq
  haveI := he
  have hκ : IsNilDP (epsDP k) := isDPNilpotent_squareZero _
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  have hred : m₁.φ₂ ≫ φ₂ = m₂.φ₂ := by
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, ← Category.assoc, m₁.sq.1, Category.assoc, hφ, m₂.sq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, m₁.sq.2, Category.assoc, hφ, m₂.sq.2]
  have hP' : (o₂.P.pull φ₂).IsLB := pull_isLB o₂.isLB φ₂
  have axis : ∀ (u v : o₁.A ⟶ o₁.A) (u' v' : o₂.A ⟶ o₂.A),
      (lift u v).left ≫ φ₂ = e.hom.left ≫ (lift u' v').left → Triv (ev o₂.P u' v') →
        Triv (ev (o₂.P.pull φ₂) u v) := by
    intro u v u' v' hc h
    rw [triv_ev_iff hP', evc, cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hc, GlobalTheory.CechPic.pull_comp]
    rw [triv_ev_iff o₂.isLB, evc] at h
    rw [h, map_zero]
  have t₁ : Triv (ev (o₂.P.pull φ₂) (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)) := by
    refine axis _ _ (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) ?_ o₂.rig₁
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd]
      simp
  have t₂ : Triv (ev (o₂.P.pull φ₂) (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)) := by
    refine axis _ _ (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) ?_ o₂.rig₂
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst]
      simp
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
  have e' : LBIso ((o₂.P.pull φ₂).pull m₁.φ₂) o₀.P := by
    refine (cls_eq_iff (pull_isLB hP' _) o₀.isLB).1 ?_
    rw [cls_pull hP', cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hred,
      ← cls_pull o₂.isLB m₂.φ₂ (pull_isLB o₂.isLB _)]
    exact (cls_eq_iff _ _).2 (LBIso.symm m₂.pol)
  have hL : (o₁.P.pull (lift (𝟙 o₁.A) (𝟙 o₁.A)).left).IsLB := pull_isLB o₁.isLB _
  exact GlobalTheory.BirigidLift.lift_unique (κ := epsDP k)
    (grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting) GlobalTheory.T.dualAbelianScheme_exists_biduality hκ hπ rfl
    o₁.ab hg o₁.ab hg m₁.cart m₁.cart m₁.sq.1 m₁.sq.2 hL o₁.ample hL o₁.ample o₀.isLB o₁.isLB o₁.rig₁ o₁.rig₂
    (LBIso.symm m₁.pol) hP' t₁ t₂ e'

end GlobalTheory.UPel.HT.PolIsoLift
