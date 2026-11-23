import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def PhaseAtRep : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)).Finite ∧
    PairVal.phasePair (gS D) L U = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

def PhaseLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D,
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

end Steps

variable (D : Formalism.BasicNotions.D7) in

def PsiProdE : Prop :=
  ∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem trace_neg_div (E : Type) [Field E] [NumberField E] (s : E) (g : ℕ) :
    Algebra.trace ℚ E (-(s / (g : E))) = -(Algebra.trace ℚ E s / (g : ℚ)) := by
  have hg : ((g : ℕ) : E) = algebraMap ℚ E (g : ℚ) := by simp
  rw [hg, div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_neg, LinearMap.map_smul, smul_eq_mul]
  ring

theorem phaseAtRep_of (hL : PhaseLoc M δ u u' F0 what₂) (hP : PsiProdE D) : PhaseAtRep M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN
  have hfun : (fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)) = fun p =>
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) :=
    funext (hL γ w F' L U hrel hgen hN)
  rw [hfun]
  obtain ⟨hf, hp⟩ := hP (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))
  refine ⟨hf, ?_⟩
  rw [hp, trace_neg_div, map_add]
  unfold PairVal.phasePair PairVal.psiInf
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseProd_of (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hW : PairVal.PhaseWellDef D u u' F0 what₂) (hR : PhaseAtRep M δ u u' F0 what₂) : PhaseProd M δ u u' F0 what₂ := by
  intro γ w hγ
  have hrel := PCount.eligRel_holds γ w hγ
  have hex := normRepElig_of hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dif_pos hex]
  have hpt : ptT γ = hex.choose.1 := by
    unfold ptT nrep
    rw [dif_pos hex]
  have hw : hex.choose.1 = w := hpt.symm.trans (FCount.ptT_eq hN hrows hγ hrel)
  have h0 : PairVal.NormRep γ w hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 := by
    have := hex.choose_spec
    rw [hw] at this
    exact this
  obtain ⟨hf, hp⟩ := hR γ w _ _ _ hrel hγ.1.1 h0
  have hyT : ∀ p, yT M δ u u' F0 what₂ γ p =
      CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) hex.choose.2.1) * sgnP p := fun p => by
    unfold yT; rw [hz]
  simp only [hyT]
  refine ⟨hf, ?_⟩
  rw [← hp]
  have hex1 : ∃ x : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D,
      PairVal.NormRep γ w x.1 x.2.1 x.2.2 := ⟨(hex.choose.2.1, hex.choose.2.2.1, hex.choose.2.2.2), h0⟩
  unfold PairVal.phaseAt
  rw [dif_pos hex1]
  exact hW γ w hrel _ _ _ _ _ _ hex1.choose_spec h0

end Assembly

end Formalism.L2.SG.Pf.Coef
