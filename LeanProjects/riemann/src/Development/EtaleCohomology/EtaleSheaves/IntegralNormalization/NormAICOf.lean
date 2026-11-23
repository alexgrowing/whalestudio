import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.OpenPf
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.AlgClosedOfAic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf.AICPf

def AffAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g] (U : W.Opens), IsAffineOpen U →
  GlobalTheory.EtC.AIC Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U)

def LocAIC : Prop := ∀ (X : Scheme.{0}) [IsIntegral X],
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ GlobalTheory.EtC.AIC Γ(X, U)) → AICSch X

theorem normAIC_of (ha : AffAIC) (hl : LocAIC) : NormAIC := by
  intro K _ _ W g _ _
  refine ⟨inferInstance, ?_⟩
  have := hl g.normalization ?_
  · exact this.2
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.fromNormalization x)) isOpen_univ
  exact ⟨g.fromNormalization ⁻¹ᵁ U, hxU, hU.preimage _, ha K g U hU⟩

theorem norm_full (ha : AffAIC) (hl : LocAIC) : LateralTheory.E.ChowCut.Norm :=
  Norm_of OpenPf.openNbhdIC FFPf.ffAlg (normAIC_of ha hl)

end LateralTheory.E.NormPf.AICPf

end
