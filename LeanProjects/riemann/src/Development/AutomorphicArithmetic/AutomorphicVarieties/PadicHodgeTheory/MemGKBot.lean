import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BasisOfUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFilStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

theorem mem_Dcr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bcr l) :
    x ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g x = x := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_Ddr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bdr l) :
    x ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g x = x := by
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_GK_bot (g : GQ l) : g ∈ GK (botExt l) := by simp [GK, botExt]

variable {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

theorem char_cr (κ : GQ l →* Eˣ) (h : IsCr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bcr l, (∀ g, actC (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Dcr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hdom : IsDomain (PP l).R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  have hc := (isCrField (botExt l) _).1.1 ((isCrIff (botExt l) _).1.1 h)
  have hf : GlobalTheory.RegularRing.FracInv ((PP l).PD (botExt l)) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l _ _ T _ y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [(PP l).PD_actB, (PP l).PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit ((PP l).PD (botExt l)) := by
    intro b hb h
    refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l _ _ T).1 (botExt l) b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← (PP l).PD_actB (botExt l) ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.exists_sum_of_isCrys _ hf hu _ hc 1
  have h0 : finrank ℚ_[l] ↥(K0 (botExt l)) = 1 := by
    rw [show K0 (botExt l) = ⊥ from bot_inf_eq _, IntermediateField.finrank_bot]
  rw [IsCrys, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actC (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actC actVB
    congr 2
    ext b
    exact ((PP l).PD_actB (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQ g)
    (fun b hb => ((PP l).PD L).invB b fun g => by rw [(PP l).PD_actB]; exact hb g) (fun g => (κ g : E))
    (actC (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulC E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Dcr _ _ _).1 hy)

theorem char_dr (κ : GQ l →* Eˣ) (h : IsDr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bdr l, (∀ g, actD (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Ddr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥L.1, y = smulD E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.RegularRing.isField_of_tied T
  have := hF.nontrivial
  have hc := (isCrField (botExt l) _).2.1.1 ((isCrIff (botExt l) _).2.1 h)
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ _ hF hc 1
  have h0 : finrank ℚ_[l] ↥(botExt l).1 = 1 := IntermediateField.finrank_bot
  rw [IsDR, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actD (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actD actVdR
    congr 2
    ext b
    exact ((PP l).PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQdR g)
    (fun b hb => ((PP l).PD L).invdR b fun g => by rw [(PP l).PD_actdR]; exact hb g) (fun g => (κ g : E))
    (actD (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulD E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Ddr _ _ _).1 hy)

end UpperTheory.V.Loc.R0
