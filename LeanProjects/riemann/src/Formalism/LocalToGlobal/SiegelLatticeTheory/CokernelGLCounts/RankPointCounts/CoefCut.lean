import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

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

def yT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : MatP D p :=
  CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p

def LocClsE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    IntP M p (yT M δ u u' F0 what₂ γ p) ∧ InOrbP δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def PhCls : Prop :=
  ∀ (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Y' : MatP D p), (M p).OK →
    IntP M p Y → InOrbP δ T T' p w Y → InOrbP δ T T' p w Y' → Y' ∈ kkOrb M p Y →
    phL M δ T T' p w Y' = phL M δ T T' p w Y

def PhaseProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)).Finite ∧
    PairVal.phaseAt γ w = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def VolProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite ∧
    (PairVal.vRdef D u u' F0 what₂ δ M γ : ℂ) =
      ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) *
        ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)

end Steps

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem repL_spec' {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {O : Set (MatP D p)}
    (h : IsLCls M δ T T' p w O) :
    IntP M p (repL M δ T T' p w O) ∧ InOrbP δ T T' p w (repL M δ T T' p w O) ∧ O = kkOrb M p (repL M δ T T' p w O) := by
  unfold repL; rw [dif_pos h]; exact h.choose_spec

theorem wtL_congr {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y Y' : MatP D p}
    (h : kkOrb M p Y = kkOrb M p Y') : wtL M δ T T' p w Y = wtL M δ T T' p w Y' := by
  unfold wtL; rw [h]

theorem hL_at {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y : MatP D p}
    (hPC : PhCls M δ) (hOK : (M p).OK) (hY : IntP M p Y) (hO : InOrbP δ T T' p w Y) :
    hL M δ T T' p w (kkOrb M p Y) = phL M δ T T' p w Y * (wtL M δ T T' p w Y : ℂ) := by
  have hcls : IsLCls M δ T T' p w (kkOrb M p Y) := ⟨Y, hY, hO, rfl⟩
  obtain ⟨-, hrO, hrE⟩ := repL_spec' hcls
  unfold hL
  rw [if_pos hcls]
  generalize repL M δ T T' p w (kkOrb M p Y) = R at hrO hrE ⊢
  have hmem : R ∈ kkOrb M p Y := by
    rw [hrE]; exact PCount.mem_kkOrb_self p R
  rw [hPC T T' p w Y R hOK hY hO hrO hmem, wtL_congr hrE.symm]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coefProd_of (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂) (hPC : PhCls M δ) (hP : PhaseProd M δ u u' F0 what₂)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨hPf, hPe⟩ := hP γ w hγ
  obtain ⟨hVf, hVe⟩ := hV γ w hγ
  have hfac : ∀ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p) =
      phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) *
        (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) := by
    intro p
    obtain ⟨hyI, hyObP⟩ := hC γ w hγ p
    show hL M δ (D.mem u).A.T (D.mem u').A.T p w (kkOrb M p (yT M δ u u' F0 what₂ γ p)) = _
    exact hL_at hPC (hA p).1 hyI hyObP
  unfold PairVal.cAt
  rw [hPe, hVe, finprod_congr hfac, finprod_mul_distrib hPf hVf]
  ring

end Assembly

end Formalism.L2.SG.Pf.Coef
