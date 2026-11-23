import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.ZsVolCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StabInCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ CZ M δ u u' (ZhatL (lf D F0) F') L

def OrbActE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∃ (X : Type) (_ : MulAction (CZ M δ u u' (ZhatL (lf D F0) F') L) X) (x : X),
      MulAction.stabilizer (CZ M δ u u' (ZhatL (lf D F0) F') L) x =
        (PairVal.stabAut D u u' F0 what₂ γ F' L).subgroupOf (CZ M δ u u' (ZhatL (lf D F0) F') L) ∧
      Nonempty (MulAction.orbit (CZ M δ u u' (ZhatL (lf D F0) F') L) x ≃
        PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F'))

def OrbFinE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Finite

theorem orbStabE_of (h1 : StabInCZ M δ u u' F0 what₂) (h2 : OrbActE M δ u u' F0 what₂) (h3 : OrbFinE M δ u u' F0 what₂) :
    OrbStabE M δ u u' F0 what₂ (CZ M δ u u') := by
  intro γ w F' L U hH
  obtain ⟨X, inst, x, hstab, ⟨e⟩⟩ := h2 γ w F' L U hH
  have hidx : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (CZ M δ u u' (ZhatL (lf D F0) F') L) =
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  refine ⟨h1 γ w F' L U hH, hidx, ?_⟩
  have hne : (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Nonempty :=
    ⟨(e ⟨x, MulAction.mem_orbit_self x⟩).1, (e ⟨x, MulAction.mem_orbit_self x⟩).2⟩
  exact ((Set.ncard_pos (h3 γ w F' L U hH)).2 hne).ne'

end Formalism.L2.SG.Pf.ZsVolOrb

end
