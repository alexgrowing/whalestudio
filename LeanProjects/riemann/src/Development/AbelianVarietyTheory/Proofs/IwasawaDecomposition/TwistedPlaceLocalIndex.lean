import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceWeightPositiveStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem atMem_imp {hL : GlobalTheory.Published.LocalLanglandsGL} {p q : LayP hL} (h : AtMem hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : AtMem hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

theorem exists_loc : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → ∃ i : (w.D Z).nd.Loc, (w.D Z).nd.w i = v ∧ (w.D Z).nd.j i = j :=
  fun hP hL => atMem_imp (GlobalTheory.T.twisted_place_weight_positive hP hL) fun _ _ _ _ w Z _ _ t _ _ c h v hv j h1 h2 σ hσ => by
    have hl := h v hv j h1 h2 σ hσ
    obtain ⟨f, -, hf⟩ := thetaT_ne_of_lamTr (D := w.D Z) (hl.trans_eq (t.r.Y.lam _ j h1 h2 σ hσ))
    exact exists_loc_of_thetaT c.a.all.cover hv h1 h2 ⟨f, hf⟩

end GlobalTheory.HeightCounting.Up.LocEx

end
