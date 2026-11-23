import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelSumOfClassData
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GShiftRowGenMonomial

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem vt_nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (by have := h hab; omega)

theorem vt_deltaLTw_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    deltaLTw O Kf m lam g ≤ nablaLTw O Kf m lam g := by
  unfold deltaLTw nablaLTw
  apply Submodule.map_mono
  unfold deltaL nablaL
  apply Submodule.comap_mono
  apply Submodule.map_mono
  exact weylLeDual O (m + 1) (m + 1) le_rfl (nuOf lam) (vt_nuOf_antitone hlam)

theorem lowest_invariant_le_delta {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) ≤ deltaLTw O Kf m lam g := by
  unfold Dl0
  rw [if_pos hlam]
  exact iInf₂_le g ⟨hg, rfl⟩

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def vt_G (P : Places p O Kf) : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := PEmpty
  lev := fun x => x.elim
  e := 0

theorem vt_HtenW_le (P : Places p O Kf) (v : Fin P.nV) (Lv : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
    (hLv : IsLattice (P.W v) Lv) :
    ∀ z ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val Lv), z ∈ Vsp Kf (P.lam0 v) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  have hle : HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) ≤
      (Vsp Kf (P.lam0 v)).restrictScalars O := by
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone (P.lam0 v) (P.dom v) s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    have e : extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g) = colSpan O (la_tw (P.ι v) (P.σ v) s.val g) :=
      la_extO_G (vt_G P) v s.val g
    rw [e] at h1
    have hd := la_tw_det (P.ι v) (P.σ v) s.val g hg
    exact la_nablaLTw_le _ _ _ hd _ (vt_deltaLTw_le O Kf _ _ hanti _ (lowest_invariant_le_delta _ _ hanti _ hd h1))
  exact fun z hz => hle hz

theorem vt_HtupW_le (P : Places p O Kf) (L : P.Tup) (hL : P.IsLatTup L) : ∀ z ∈ P.HtupW L, z ∈ P.Vtup := by
  have hle : P.HtupW L ≤ P.Vtup.restrictScalars O := by
    unfold Places.HtupW Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, fun v => vt_HtenW_le P v (L v) (hL v) _ (hF v), rfl⟩
  exact fun z hz => hle hz

end Formalism.MainNotions.FormalGroupSystem.Pf

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem vt_FQ {p : ℕ} [Fact p.Prime] (X : Sys p) {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j)
    (L : (X.Pj j).Tup) : F c L ∈ (X.Pj j).Vtup := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    have h := (mem_Int_iff X j x).1 hx
    by_cases hL : (X.Pj j).IsLatTup L
    · exact vt_HtupW_le (X.Pj j) L hL _ (h.1 c L hL)
    · rw [h.2.1 c L hL]; exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
