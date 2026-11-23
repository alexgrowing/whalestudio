import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SameOrbEquivalence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.CosExt

set_option maxHeartbeats 4000000 in

theorem exists_qExt_cos : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  intro D c v B PP G χ hc δ hδ η hη hμ A hA M hM C _ cs hinj hall
  obtain ⟨E, rfl, rfl, rfl, rfl, -⟩ := GlobalTheory.QTw.Inh.exists_ext_of_reps D c v B PP G χ hc δ hδ η hη hμ A hA M hM
  classical
  let Ch' : ℕ → Type := fun j => if j = G.s + 1 then C else if G.s + 1 + 1 < j then Unit else E.Ch j
  have eC : Ch' (G.s + 1) = C := if_pos rfl
  have eE : ∀ j, j ≤ G.s + 1 + 1 → j ≠ G.s + 1 → Ch' j = E.Ch j := fun j h1 h2 => by
    simp only [Ch', if_neg h2, if_neg (not_lt.2 h1)]
  have eU : ∀ j, G.s + 1 + 1 < j → Ch' j = Unit := fun j h1 => by
    simp only [Ch', if_neg (show j ≠ G.s + 1 by omega), if_pos h1]
  let fC : ∀ j, Fintype (Ch' j) := fun j => by
    simp only [Ch']; split_ifs <;> infer_instance
  let rep' : ∀ j d, j + d = G.s → Ch' j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k :=
    fun j d h x => E.rep j d h (cast (eE j (by omega) (by omega)) x)
  let cos' : Ch' (G.s + 1) → (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ E.M) :=
    fun y => Submodule.Quotient.mk (cs (cast eC y))
  have hpen : ∀ (α : Ch' G.s) (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl) e
      ((G.T E.δ E.tame E.η).xiPen (box _ (G.ϖ ^ E.M)) (rep' G.s 0 rfl α) (cos' y)) :=
    fun α y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  have htop : ∀ (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX (G.s + 1) le_rfl) G.FM e
      ((G.T E.δ E.tame E.η).xiTop (box _ (G.ϖ ^ E.M)) G.ψk G.ν (-1) (cos' y)) :=
    fun y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  choose dPen hdPen using hpen
  choose dTop hdTop using htop
  let dL' : ∀ j, Ch' j → Ch' (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ := fun j =>
    if h : j + 1 ≤ G.s then fun α γ => E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
    else if h' : j = G.s then (by subst h'; exact dPen)
    else if h'' : j = G.s + 1 then (by subst h''; exact fun y _ => dTop y)
    else fun _ _ => 0
  let wt' : ∀ j, Ch' j → ℂ := fun j =>
    if h : j = G.s + 1 then (by subst h; exact fun y => (E.idx (G.s + 1) : ℂ) *
      (Nat.card {yb | SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (cos' y) yb} : ℂ))
    else if h' : j ≤ G.s then fun α => E.wt j (cast (eE j (by omega) (by omega)) α)
    else fun _ => (E.idx (G.s + 1 + 1) : ℂ)
  let εL' : ∀ j, Ch' j → GA D (c.V j) →₀ ℂ := fun j =>
    if h : j ≤ G.s then fun α => E.εL j (cast (eE j (by omega) (by omega)) α) else fun _ => 0
  let E' : QExt G χ :=
    { δ := E.δ, tame := E.tame, η := E.η, unr := E.unr, mu_comp := E.mu_comp, A := E.A, reps := E.reps, Ch := Ch', fC := fC, rep := rep'
      rep_bij := fun j d h => (E.rep_bij j d h).comp
        ((Equiv.cast (eE j (by omega) (by omega))).bijective.bijOn_univ)
      M := E.M, adapt := E.adapt, cos := cos'
      cos_inj := fun y y' h => (Equiv.cast eC).injective (hinj _ _ h)
      cos_all := fun z hz => by
        obtain ⟨y, hy⟩ := hall z hz
        exact ⟨cast eC.symm y, by simpa [cos'] using hy⟩
      one := (Fintype.card_congr (Equiv.cast (eE (G.s + 1 + 1) le_rfl (by omega)))).trans E.one
      eL := E.eL, eLT := E.eLT, eL_at := E.eL_at, eLT_at := E.eLT_at, dL := dL'
      dL_mid := fun j d H α γ => by
        have := E.dL_mid j d H (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
        have e : dL' j α γ = E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ) := by
          simp only [dL']; rw [dif_pos (show j + 1 ≤ G.s by omega)]
        rw [e]; exact this
      dL_pen := fun α y => by
        have e : dL' G.s α y = dPen α y := by
          simp only [dL']; rw [dif_neg (by omega), dif_pos trivial]
        rw [e]; exact hdPen α y
      dL_top := fun y u => by
        have e : dL' (G.s + 1) y u = dTop y := by
          simp only [dL']; rw [dif_neg (by omega), dif_neg (by omega), dif_pos trivial]
        rw [e]; exact hdTop y
      εL := εL'
      εL_at := fun j ρ hρ d h α => by
        obtain ⟨e, h1, h2⟩ := E.εL_at j ρ hρ d h (cast (eE j (by omega) (by omega)) α)
        refine ⟨e, h1, ?_⟩
        rw [← h2]; simp only [εL']; rw [dif_pos (show j ≤ G.s by omega)]
      εL_zero := fun α => by
        simp only [εL']; rw [dif_pos (Nat.zero_le _)]; exact E.εL_zero _
      idx := E.idx, idx_mid := E.idx_mid, idx_top := E.idx_top, m := E.m, haar := E.haar, wt := wt'
      wt_mid := fun j d h α => by
        rw [← E.wt_mid j d h (cast (eE j (by omega) (by omega)) α)]
        simp only [wt']; rw [dif_neg (show j ≠ G.s + 1 by omega), dif_pos (show j ≤ G.s by omega)]
      wt_pen := fun y => by simp only [wt']; rw [dif_pos trivial]
      wt_top := fun u => by simp only [wt']; rw [dif_neg (by omega), dif_neg (by omega)] }
  refine ⟨E', rfl, rfl, rfl, rfl, ⟨Equiv.cast eC.symm, fun y => ?_⟩, fun j hj => ⟨(Equiv.cast (eU j hj)).unique⟩⟩
  simp [E', cos']

end GlobalTheory.QTw.CosExt
end
