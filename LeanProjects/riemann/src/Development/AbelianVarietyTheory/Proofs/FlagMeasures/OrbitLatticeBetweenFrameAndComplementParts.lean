import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpacesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProj

set_option maxHeartbeats 1600000 in
open GlobalTheory.ThetaMove.CommonRef in
theorem lattice_between_parts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel Λ₀ hΛ₀
  have hU : ∀ y ∈ Xplus F ⊔ Xplus F', y ∈ orth (VS D) (Xplus F ⊔ Xplus F') → y = 0 := by
    intro y hyU hyW
    by_contra hy
    have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hZ hG y hyW hy
    have h0 : (VS D).hT y y = 0 := (mem_orth_iff _ y).1 hyW y hyU
    rw [h0, map_zero] at hpos
    exact lt_irrefl _ hpos
  have hdet := gram_det_isUnit _ hU
  have hcomm : ∀ p : PlF D, ∀ h ∈ (FP p).UW0, ∀ y,
      projP Z p (Xplus F ⊔ Xplus F') (h y) = h (projP Z p (Xplus F ⊔ Xplus F') y) :=
    fun p h hh y => localOrthogonalProj_comm_complementUnitary Z p F F' (FP p) (hB p).1 (hB p).2.1 h hh y
  generalize Xplus F ⊔ Xplus F' = U at hU hdet hcomm ⊢
  obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_le (full_of_span hΛ₀.span_eq_top)
    (hΛ₀.fg.map ((proj U).restrictScalars (𝓞 D.host.E)))
  have hcast : ∀ v : (VS D).V, (N : D.host.E) • v = (N : 𝓞 D.host.E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨Q, hQ⟩ : ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, Q = (N : D.host.E) • proj U := ⟨_, rfl⟩
  have hQx : ∀ x, Q x = (N : D.host.E) • proj U x := fun x => by rw [hQ]; rfl
  have hQ₀ : Λ₀.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Λ₀ := by
    rintro _ ⟨x, hx, rfl⟩
    show Q x ∈ Λ₀
    rw [hQx, hcast]
    exact hNmem _ ⟨x, hx, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro Λ hΛ hloc
  have hQp : ∀ p : PlF D, ∀ x, baseChange₂ D p (Q x) = ((N : (D.s.atP p).Ep) • projP Z p U) (baseChange₂ D p x) := by
    intro p x
    rw [hQx, LinearMap.smul_apply, baseChange_smul₂, baseChangeAt_proj Z p, map_natCast]
  have hlat' : Submodule.IsLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) :=
    ⟨hΛ.fg.sup (hΛ.fg.map _), top_le_iff.1 (hΛ.span_eq_top ▸ Submodule.span_mono (by
      intro y hy; exact Submodule.mem_sup_left hy))⟩
  have heq : Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E)) = Λ := by
    refine ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ hlat' hΛ).2 fun p => ?_
    rw [localLattice_sup, sup_eq_left, localLattice_map Z p Q _ (hQp p)]
    obtain ⟨h, hh, himg⟩ := hloc p
    obtain ⟨Qp, hQpdef⟩ : ∃ Qp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p, Qp = (N : (D.s.atP p).Ep) • projP Z p U :=
      ⟨_, rfl⟩
    rw [← hQpdef]
    have hc : ∀ y, Qp (h y) = h (Qp y) := by
      intro y
      rw [hQpdef, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hcomm p h hh y]
    have hL : (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O) ≤ lattice₂ D Z.M p Λ₀ :=
      calc (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O)
          = lattice₂ D Z.M p (Λ₀.map (Q.restrictScalars (𝓞 D.host.E))) :=
            (localLattice_map Z p Q Qp (fun x => hQpdef ▸ hQp p x) Λ₀).symm
        _ ≤ lattice₂ D Z.M p Λ₀ := localLattice_mono Z p hQ₀
    have := img_map_le Z p Qp h hc _ hL
    rwa [himg] at this
  have key : ∀ y ∈ Λ, Q y ∈ Λ := fun y hy => by
    rw [← heq]
    exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
  intro x hx
  refine Submodule.mem_sup.2 ⟨Q x, ⟨key x hx, ?_⟩, (N : D.host.E) • x - Q x, ⟨?_, ?_⟩, add_sub_cancel _ _⟩
  · show Q x ∈ U
    rw [hQx]
    exact U.smul_mem _ (proj_mem U x)
  · refine Λ.sub_mem ?_ (key x hx)
    rw [hcast]
    exact Λ.smul_mem _ hx
  · show (N : D.host.E) • x - Q x ∈ orth (VS D) U
    rw [hQx, ← smul_sub]
    exact Submodule.smul_mem _ _ (sub_proj_mem_orth U hdet x)

end GlobalTheory.FrameProj
