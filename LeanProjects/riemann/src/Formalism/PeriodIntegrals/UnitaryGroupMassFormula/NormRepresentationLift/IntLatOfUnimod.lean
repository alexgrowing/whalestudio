import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.NormRepLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.FrameActOneAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowVec (D : D7) (u : D.what₂.Word) (T' : ℕ) : Prop :=
  PrimeHyp D u T' →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ (a : Fin D.R.rS) (t : Fin (D.R.rS + 1) → 𝓞 D.host.E),
      ∃ v ∈ Λ, ∃ l : 𝓞 D.host.E, (l : D.host.E) + star (l : D.host.E) = -(VS D).hT v v ∧
        (∀ i, i ≤ a → (VS D).hT v (F0.e i) = 0) ∧
        ∀ c, Fin.castSucc a < c → ∃ q : 𝓞 D.host.E,
          (VS D).hT v (frame (lf D F0) c) = ((t c + (gS D : 𝓞 D.host.E) * q : 𝓞 D.host.E) : D.host.E)

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

def mapFlag (n : S.V ≃ₗ[E] S.V) (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (F : FlagG S r T) :
    FlagG S r T where
  e := fun a => n (F.e a)
  z := n F.z
  e_indep := F.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker
  e_iso := fun a b => by rw [hn]; exact F.e_iso a b
  z_orth := fun a => by rw [hn]; exact F.z_orth a
  z_norm := by rw [hn]; exact F.z_norm

theorem frame_mapFlag (n : S.V ≃ₗ[E] S.V) (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (F : LFlag S r T)
    (zt : S.V) (b : Fin (r + 1)) :
    frame (⟨mapFlag n hn F.fl, zt⟩ : LFlag S r T) b = n (frame F b) := by
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem intLat_of_unimod (Λ : Submodule (𝓞 E) S.V) (h : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) : IntLat Λ := by
  intro x hx y hy
  rw [← h] at hy
  have hy' : y ∈ Formalism.E.hdual S.hT Λ := hy
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hy'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hy' x hx)
  exact ⟨o, ho.symm⟩

theorem normRepStep_of (D : D7) (u u' : D.what₂.Word) (hS : TermStable D u u')
    (hP : PrimeHyp D u (Tu D u')) (hV : RowVec D u (Tu D u')) : PI.NormRepLift.NormRepStep D u u' := by
  intro F0 Λ hΛ t _ _
  obtain ⟨⟨F1, hF1⟩, rfl⟩ := Quot.exists_rep t
  obtain ⟨ξ, hAdm⟩ := hF1.2.1
  have hint : IntLat Λ := intLat_of_unimod Λ hΛ.2.1.2.1
  have hfe : ∀ a, (lf D F0).fl.e a ∈ Λ := fun a => e_mem_lam D F0 Λ hΛ a
  have hfr : ∀ c, frame (lf D F0) c ∈ Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => simpa [frame, FlagG.fvec] using hΛ.2.1.2.2.1.1
    | cast i => simpa [frame, FlagG.fvec] using hfe i
  obtain ⟨n, hn, M, hM, Q, hQ⟩ := exists_undo Λ hint (lf D F0) (gS D : 𝓞 D.host.E)
    (hV hP F0 Λ hΛ) hfe ξ ⟨hAdm.1, hAdm.2.1⟩
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn.1.1
  let F2 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) := ⟨mapFlag n hiso F1.fl, n F1.zt⟩
  have hDC : DCRel Λ (lf D F0) F1 F2 :=
    ⟨n, hn, 1, one_mem_NLam Λ F1, fun a => by simp [F2, frame_mapFlag], by simp [F2]⟩
  have hP2 : PD D Λ (lf D F0) u' F2 := hS F0 Λ hΛ ⟨F1, hF1⟩ F2 hDC
  have hq : Formalism.L2.SG.TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F2, hP2⟩ =
      Quot.mk (Formalism.L2.SG.TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u')) ⟨F1, hF1⟩ :=
    (Quot.sound (r := Formalism.L2.SG.TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u'))
      (a := ⟨F1, hF1⟩) (b := ⟨F2, hP2⟩) hDC).symm
  refine ⟨F2, ⟨hP2, hq⟩, ?_, ?_, ?_⟩
  · intro a b hab; exact Matrix.one_apply_ne (ne_of_lt hab).symm
  · intro a; exact Matrix.one_apply_eq a
  · intro b
    rw [frameAct_one, frame_mapFlag]
    have e1 : n (frame F1 b) - frame (lf D F0) b =
        n (frame F1 b - frameAct (frame (lf D F0)) ξ b) +
          (frameAct (frame (lf D F0)) (M * ξ) b - frame (lf D F0) b) := by
      rw [map_sub, actsBy_frameAct hM]; abel
    rw [e1]
    refine modG_add Λ _ (modG_map Λ _ n hn.1.2 (hAdm.2.2 b)) (modG_of_mem Λ _ ?_)
    rw [hQ, frameAct_one_add, add_sub_cancel_left]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (frameAct_mem Λ _ hfr Q b)

end PI.NRL
