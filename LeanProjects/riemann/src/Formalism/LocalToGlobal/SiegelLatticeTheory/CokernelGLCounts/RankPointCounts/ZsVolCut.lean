import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.IdxCocycle

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolCut

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.IndexCocycleOrbits
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def HypE (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D) : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧
    PrimeHyp D u (Tu D u') ∧ EligAt γ w ∧ PairVal.NormRep γ w F' L U

def stZSet (Z L : PairVal.MatR D) : Set (PairVal.GLR D) :=
  {a | ∃ a' : PairVal.GLR D, (a : PairVal.MatR D) = L⁻¹ * (a' : PairVal.MatR D) * L ∧ IsLoUni (a' : PairVal.MatR D) ∧
    ∃ b : PairVal.MatR D, IsUpUni b ∧ (a' : PairVal.MatR D) * ZhatOM Z * b = ZhatOM Z ∧
      ∀ p : PlF D, ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
        Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧
        ∀ Z' : PairVal.MatR D, CntLocal.ZZP (M := M) δ u u' p (ZhatOM ((a' : PairVal.MatR D) * ZhatOM Z' * b)) =
          l * CntLocal.ZZP (M := M) δ u u' p Z' * ρ}

def CZ (Z L : PairVal.MatR D) : Subgroup (PairVal.GLR D) := Subgroup.closure (stZSet M δ u u' Z L)

def OrbStabE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ C (ZhatL (lf D F0) F') L ∧
      (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) =
        (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ∧
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard ≠ 0

def ProdE (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D)) : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    IdxRatio (PairVal.stabInt D u u' δ M w) (C (ZhatL (lf D F0) F') L) =
      ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

theorem volIdxProd_of (hP : PrimeHyp D u (Tu D u')) (C : PairVal.MatR D → PairVal.MatR D → Subgroup (PairVal.GLR D))
    (h1 : OrbStabE M δ u u' F0 what₂ C) (h2 : ProdE M δ u u' F0 what₂ C) : VolIdxProd M δ u u' F0 what₂ := by
  intro hA hT hR γ w F' L U hE hN
  have hH : HypE M δ u u' F0 what₂ γ w F' L U := ⟨hA, hT, hR, hP, hE, hN⟩
  obtain ⟨hle, hidx, hne⟩ := h1 γ w F' L U hH
  have hne' : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (C (ZhatL (lf D F0) F') L) ≠ 0 := by
    rw [hidx]; exact hne
  have hco := Formalism.L2.SG.Pf.IndexCocycleOrbits.idxCocycle (PairVal.GLR D) (PairVal.stabInt D u u' δ M w)
    (PairVal.stabAut D u u' F0 what₂ γ F' L) (C (ZhatL (lf D F0) F') L) hle hne'
  have hv : PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
      IdxRatio (PairVal.stabInt D u u' δ M w) (PairVal.stabAut D u u' F0 what₂ γ F' L) := by rfl
  rw [hv, hco, hidx, h2 γ w F' L U hH]

end Formalism.L2.SG.Pf.ZsVolCut

end
