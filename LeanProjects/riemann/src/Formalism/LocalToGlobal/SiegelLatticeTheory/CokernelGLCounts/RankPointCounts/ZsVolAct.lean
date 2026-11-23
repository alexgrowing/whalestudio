import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerInCongruenceHolds

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAct

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def sbs {D : Formalism.BasicNotions.D7} (b : MatR D) : MatR D := Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS

def LiftData (γ : TermDef.Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Prop :=
  IsLoUni (a' : MatR D) ∧ IsUpUni b ∧ (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') ∧
    Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b ∧
    ν ∈ NLam γ.lam (lf D F0) ∧ m ∈ NLam γ.lam F' ∧
    (∀ c, ν (frame (lf D F0) c) = ∑ d, (a' : MatR D).conjTranspose d c • frame (lf D F0) d) ∧
    (∀ c, m (frame F' c) = ∑ d, sbs b d c • frame F' d) ∧
    F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') ∧
    TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F₂ ∧
    ∀ c, frame F₂ c = ν⁻¹ (m (frame F' c))

def MoveCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a' : GLR D) (b : MatR D), IsLoUni (a' : MatR D) → IsUpUni b →
      (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') →
      Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b →
      ∃ ν m F₂, LiftData u u' F0 what₂ γ F' a' b ν m F₂

def OntoCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F'),
      TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'' →
      ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V), LiftData u u' F0 what₂ γ F' a' b ν m F''

def FibreCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
      (x₁ x₂ : GLR D), (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L → (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L →
      LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁ → LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂ →
      (CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ ↔ x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L)

end Formalism.L2.SG.Pf.ZsVolAct

end
