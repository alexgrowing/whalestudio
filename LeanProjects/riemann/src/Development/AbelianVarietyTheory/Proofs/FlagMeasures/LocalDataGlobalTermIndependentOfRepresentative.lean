import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermsSameDoubleCosetSameLocalDataStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.RepIndep

open GlobalTheory.LoopC.PairMove GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem xsp_map_of_frame {F₁ F₂ : LFlag S r T'} (f : S.V ≃ₗ[E] S.V) (h : ∀ a, frame F₂ a = f (frame F₁ a)) :
    (Xsp F₁).map (f : S.V →ₗ[E] S.V) = Xsp F₂ := by
  change (Submodule.span E (Set.range F₁.fl.e)).map _ = Submodule.span E (Set.range F₂.fl.e)
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  have : (f : S.V →ₗ[E] S.V) ∘ F₁.fl.e = F₂.fl.e := by
    funext b
    have := h b.castSucc
    rw [Formalism.L2.SG.Pf.frame_castSucc_td, Formalism.L2.SG.Pf.frame_castSucc_td] at this
    simp [this]
  rw [this]

theorem iota_of_dc {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (g : ℕ)
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = (n * m) (frame F₁ a)) :
    IotaCompat Λ F F₁ F₂ (n * m) g := by
  have hmX : (Xsp F₁).map (m : S.V →ₗ[E] S.V) = Xsp F₁ := nlam_map hm
  have hnmX := xsp_map_of_frame (n * m) hfr
  have hnX : (Xsp F₁).map (n : S.V →ₗ[E] S.V) = Xsp F₂ := by
    refine map_of_mem_iff fun x => ?_
    have e : n x = (n * m) (m.symm x) := by simp [LinearEquiv.mul_apply]
    rw [e, mem_iff_of_map hnmX, mem_iff_of_map (map_symm hmX)]
  have hi : n⁻¹ ∈ NLam Λ F := Formalism.L2.SG.Pf.nlamPf_inv hn
  intro x' hx' l hl
  have e : l - (n * m) x' = n (n⁻¹ l - m x') := by
    rw [map_sub]
    simp [LinearEquiv.mul_apply]
  rw [e, ngx_iff hn.1 (nlam_map hn) hnX g]
  have e2 : n⁻¹ l - m x' = (l - x') + ((n⁻¹ l - l) - (m x' - x')) := by abel
  rw [e2]
  refine (Submodule.add_mem_iff_left _ ?_).symm
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨?_, hi.2.2 l hl.2⟩)
    exact Λ.sub_mem ((aut_mem_iff hi.1 l).2 hl.1) hl.1
  · refine Submodule.mem_sup_right ⟨?_, hm.2.2 x' hx'.2⟩
    exact Λ.sub_mem ((aut_mem_iff hm.1 x').2 hx'.1) hx'.1

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rep_indep : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → DCRel Λ (lf D F0) F₁ F₂ → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) ↔ Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ h1 h2 hG hdc p P hP d
  have key : ∀ A B : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' A → PD D Λ (lf D F0) u' B →
      Gval (lf D F0) A ≠ 0 → DCRel Λ (lf D F0) A B →
      Over P d (locU Z p Λ (lf D F0) A (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) B (Tu D u) (Tu D u')) := by
    intro A B hA hB hGA hAB
    obtain ⟨n, hn, m, hm, hfr, -⟩ := hAB
    exact GlobalTheory.T.global_terms_same_doubleCoset_same_local_data D Z u u' F0 Λ hΛ A B hA hB hGA n ⟨hn.1.1, hn.2.1, hn.2.2⟩ m ⟨hm.1.1, hm.2.1, hm.2.2⟩
      (Formalism.L2.SG.Pf.isAutLam_mul hn.1 hm.1).2 (fun a => hfr a) (iota_of_dc (gS D) hn hm (fun a => hfr a)) p P hP d
  refine ⟨key F₁ F₂ h1 h2 hG hdc, key F₂ F₁ h2 h1 ?_ (Formalism.L2.SG.Pf.dcrel_symm _ _ hdc)⟩
  rw [Formalism.L2.SG.Pf.gval_rel (h := hdc)]
  exact hG

end GlobalTheory.LocOver.RepIndep
