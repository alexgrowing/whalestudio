import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolShape
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolOrb

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolIn

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Formalism.L2.SG.Pf.ZsVolShape Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def FrameShapeP : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ s ∈ NLam γ.lam (lf D F0) ∩ NLam γ.lam F', ∀ uu uu' : MatR D, IsUpUni uu → IsUpUni uu' →
      (∀ b, s (F0.fvec b) = ∑ c, uu c b • F0.fvec c) → (∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c) →
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D uu.conjTranspose
          (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS)

theorem stabInCZ_of (hF : FrameShapeP M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolOrb.StabInCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hP.1.pos.ne'
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  refine (Subgroup.closure_le _).2 ?_
  rintro a ⟨s, ⟨hsF, hsF'⟩, uu, huu, ha⟩
  have hsF0 := hsF
  have hsF'0 := hsF'
  obtain ⟨⟨hiso, _⟩, hf1, hf2⟩ := hsF
  obtain ⟨⟨_, _⟩, hg1, hg2⟩ := hsF'
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 huu hu0
  subst heq
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
  let a' : GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : MatR D) = uu.conjTranspose := rfl
  have hshape := hF γ w F' L U ⟨hA, hT, hR, hP, hE, ⟨‹_›, ‹_›, hL, hU, hZ⟩⟩ s ⟨hsF0, hsF'0⟩ uu uu' huu0 huu' hu0 hu'
  have hmem : a ∈ stZSet M δ u u' (ZhatL (lf D F0) F') L := by
    refine (mem_stZSet_iff M δ u u' hA _ L a).2 ⟨a', by rw [ha', ha], by rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS, Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn huu', ?_, by rw [ha']; exact hshape⟩
    rw [ha', Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]
    show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
      (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) = Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS
    rw [show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
        (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      uu.conjTranspose * Zhat F0 F'.fl * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * uu' *
        Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS by simp only [Matrix.mul_assoc],
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one, ← hZc]
  exact (mem_CZ M δ u u' _ L hLd a).2 hmem

end Formalism.L2.SG.Pf.ZsVolIn

end
