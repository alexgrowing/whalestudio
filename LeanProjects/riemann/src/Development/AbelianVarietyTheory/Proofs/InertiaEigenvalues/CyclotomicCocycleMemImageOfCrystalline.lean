import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Xstab
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (((HW l).W K s LL h).GKs : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥((HW l).W K s LL h).GKs := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  letI := τ
  haveI hT2 : T2Space (TW (RW LL) T) := hτ.1
  have hTG : IsTopologicalAddGroup (TW (RW LL) T) := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let a : ↥((HW l).W K s LL h).GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
    (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
  have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
    fun g x => rfl
  have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
    intro g g' x
    simp only [ha1]
    exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
      (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
  have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
    GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
  have haj : ∀ g (w : ((HW l).W K s LL h).DD T), a g (((F l).E K s LL h).tie.jD T w) =
      ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ (g : ↥(GK K))) w) :=
    fun g w => (((F l).E K s LL h).tie.jD_act T (g : ↥(GK K)) w).symm
  let J : AddSubgroup (TW (RW LL) T) :=
    (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X).toAddSubgroup.map (((F l).E K s LL h).tie.jD T).toAddMonoidHom
  have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X,
      ((F l).E K s LL h).tie.jD T w = x := fun x => AddSubgroup.mem_map
  have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
    have : (J : Set (TW (RW LL) T)) = ((F l).E K s LL h).tie.jD T ''
        (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T)) := by
      ext x
      exact (hJm x).trans Iff.rfl
    rw [this]; exact hclo
  have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
    intro g x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj]
    exact (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1, rfl⟩
  have hJk : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
    intro h' hh x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj, hl1 h' hh, ((HW l).W K s LL h).γD_one]
  haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
  haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
  haveI hCS : ContinuousSub (TW (RW LL) T) :=
    ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
  have hZc : Continuous (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) := by
    unfold Zf
    exact (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
      (((hact b).comp continuous_subtype_val).sub continuous_const)
  have hZm : ∀ g g', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b (g * g') =
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g + a g (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g') := by
    intro g g'
    have e : (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
        ⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
          ⟨T.ρ (g : ↥(GK K)) ((c : ↥((HW l).W K s LL h).GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
      Subtype.ext (c.2.1.2 g g')
    have hz : ∀ g'', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g'' =
        (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g'', GlobalTheory.HerrClassMaps.mem_T c g''⟩ : ↥T.L.T) +
          (a g'' b - b) := fun _ => rfl
    simp only [hz, map_add, map_sub, ha1t, hamul, e, TensorProduct.tmul_add]
    abel
  have hZk' : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b h' = 0 :=
    fun h' hh => hZk h' (hl1 h' hh)
  have hzJ : ((F l).E K s LL h).tie.jD T z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
