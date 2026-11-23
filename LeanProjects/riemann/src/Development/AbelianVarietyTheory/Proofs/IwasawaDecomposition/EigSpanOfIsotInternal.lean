import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigAdOfRowEig
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEigMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAllStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

theorem exists_eigAd_of_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine (StepW.and (eigAd_of_rowEig hL) GlobalTheory.HeckeField.Gap.rowEig_mem_fixedField).trans (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx hL' h3 h5
  classical
  refine ⟨fun j σ k Pl => if h : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) j) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) j) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) then h.choose else 0,
    H.1 P x hx _ ?_⟩
  intro i σ k Pl α Rr hk hg h0
  have t2 := H.2 P x hL' h3 h5 i σ k Pl α Rr hk h0
  have hI := congrArg (fun i' : Fin (Dof x).R.m => hkNorm x.m.z.R i' k Pl *
      GlobalTheory.EigRows.rowEig x.r.Y i' σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) (NX.idxOf_succ (Dof x) i)
  have hex : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) (i.1 + 1)) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) (i.1 + 1)) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) :=
    let ⟨c, hc⟩ := t2; ⟨c, hc.trans hI.symm⟩
  refine Eq.trans ?_ (hex.choose_spec.trans hI)
  simp only [dif_pos hex]

theorem eig_span_of_isotInternal : PrN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig ∧ SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hN hIso hL
  refine (StepW.and (StepW.and (exists_eigAd_of_state hL) (GlobalTheory.T.stable_hecke_level_character hL)) (StepW.and (GlobalTheory.T.good_fiber_types_all hN hL) hIso)).trans
    (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx θ hL' h1 h2 h3 h4 h5
  obtain ⟨eig, he⟩ := H.1.1 P x hx hL' h3 h5
  exact ⟨eig, he, H.1.2 P x hx (H.2.2 P x) (GlobalTheory.EigRows.occGood_of_all _ (H.2.1 P x hx)) θ hL' h1 h2 h3 h4 h5 eig he⟩

theorem eig_span_of_state : GlobalTheory.Published.DiscreteSeriesUpqUnique → PrN → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig ∧ SpanC (SOf x) (SbD (Dof x)) θ hL' eig :=
  fun _ hN _ hIso => eig_span_of_isotInternal hN hIso

end GlobalTheory.HeightCounting.RatSide
