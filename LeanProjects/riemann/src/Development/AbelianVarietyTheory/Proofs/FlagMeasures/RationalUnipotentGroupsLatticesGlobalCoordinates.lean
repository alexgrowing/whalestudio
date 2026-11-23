import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentConjIffOfUnitriangularIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnipotentFrameCorrespondsUnderIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRationalUnipotentOfLocalExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToDeterminesUnipotentFactorisationStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GrpCoord

theorem rat_iff (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G)
    {T₁ : D.host.E} (F₁ : LFlag (VS D) D.R.rS T₁) (g : ∀ p, Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ p a, g p a = (c.c p).e (scaled Z p (frame F₁) a)) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    γ ∈ NRat F₁ ↔ (c.e.symm.trans γ).trans c.e ∈ (placesOf Z).rat (fun p => (G.S p).Nof (g p)) := by
  have hgf : ∀ p, g p = fun a => (c.c p).e (scaled Z p (frame F₁) a) := fun p => funext (hg p)
  constructor
  · intro hγ p
    obtain ⟨h, hext, -, -, -, hNU⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ.1
    let k := ((c.c p).e.symm.trans h).trans (c.c p).e
    have hk : k ∈ (G.S p).Nof (g p) := by
      rw [hgf p]; exact (GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p) _ h).1 (hNU F₁ hγ)
    refine ⟨k, hk, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := c.e.surjective x
      have h1 : (placesOf Z).bc p (c.e y) = (c.c p).e (baseChange₂ D p y) := (c.compat p y).symm
      have h2 : ((c.e.symm.trans γ).trans c.e) (c.e y) = c.e (γ y) := by simp
      rw [h2, h1, ← c.compat p (γ y), ← hext y]
      show (c.c p).e (h ((c.c p).e.symm ((c.c p).e (baseChange₂ D p y)))) = _
      rw [LinearEquiv.symm_apply_apply]
  · intro hγ
    have hne : Nonempty (PlF D) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField _)⟩⟩
    obtain ⟨p⟩ := hne
    obtain ⟨g₀, hg'N, hg'E⟩ := hγ p
    let g' : type_of% ((c.c p).e.symm.trans (c.c p).e) := g₀
    let h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p := ((c.c p).e.trans g').trans (c.c p).e.symm
    have hconj : ((c.c p).e.symm.trans h).trans (c.c p).e = g' := by
      ext x; simp [h]
    have hN : h ∈ NU (locH Z p) (scaled Z p (frame F₁)) := by
      rw [GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p), hconj, ← hgf p]; exact hg'N
    refine GlobalTheory.T.mem_rationalUnipotent_of_local_extension D Z p F₁ γ h ?_ hN
    intro y
    have h1 : (c.c p).e (baseChange₂ D p y) = (placesOf Z).bc p (c.e y) := c.compat p y
    have h3 : g₀ ((placesOf Z).bc p (c.e y)) = (placesOf Z).bc p (c.e (γ y)) :=
      (hg'E _).trans (by simp)
    show (c.c p).e.symm (g₀ ((c.c p).e (baseChange₂ D p y))) = baseChange₂ D p (γ y)
    rw [h1, h3, ← c.compat p (γ y), LinearEquiv.symm_apply_apply]

theorem grp_eq {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp σ n = (c.e.symm.trans (σ * n * σ⁻¹)).trans c.e := by
  ext x; simp [GCoord.grp]

theorem frame_mapLF (D : D7) {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) : frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF; rw [dif_pos hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast b => simp [frame, FlagG.fvec, mapFlag]

theorem grp_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (∀ n, n ∈ NRat (lf D (X.Fu u)) ↔ c.grp ρ n ∈ G.N) ∧ (∀ m, m ∈ NRat (lf D (X.Fu u')) ↔ c.grp (ρ * t₀.lin) m ∈ G.N') ∧ (∀ (σ n : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) Λ, c.lat (σ * n) Λ = (c.lat σ Λ).map (((c.grp σ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) ∧ (∀ (σ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (x : G.GLV), ∃ n, c.grp σ n = x) ∧ (∀ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∀ (p : PlF D) g Λ, GlobalTheory.LocOver.Ext p σ g → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Y.M p) g (lattice₂ D Y.M p Λ))) ∧ ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hAB G c t₀ ρ U U' hmv
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := hmv
  have hN : G.N = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F00) a))) := by
    unfold GFrames.N Frames.N
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f_eq, (hAB p).1.1]
  have hN' : G.N' = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F'0) a))) := by
    unfold GFrames.N' Frames.N'
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f'_eq, (hAB p).1.2.1]
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  refine ⟨fun n => ?_, fun m => ?_, fun σ n Λ => ?_, fun σ x => ?_, fun σ _ p g Λ hg => ?_, ?_⟩
  · refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F00 ρ U hρ hU hF n).trans ?_
    rw [grp_eq, hN]
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · have hF2 : ∀ b, (ρ * t₀.lin) (frame (lf D (X.Fu u')) b) = ∑ a, U' a b • frame F'0 a := by
      intro b
      rw [← hF' b]
      show ρ (t₀.lin _) = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) b)
      rw [frame_mapLF D _ hlin]
    refine (GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry D _ F'0 (ρ * t₀.lin) U' (Subgroup.mul_mem _ hρ hlin) hU' hF2 m).trans ?_
    rw [grp_eq, hN']
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · unfold GCoord.lat
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp [GCoord.grp]
  · refine ⟨((σ.trans c.e).trans x).trans (σ.trans c.e).symm, ?_⟩
    ext y; simp [GCoord.grp]
  · exact GlobalTheory.T.completion_moved_lattice_eq_local_coordinates D _ F00 F'0 FP G c σ p g Λ hg
  · exact GlobalTheory.T.moves_to_determines_unipotent_factorisation D X Y u u' F00 F'0 t₀ ρ U U' ⟨hρ, hU, hU', hF, hF'⟩

end GlobalTheory.HL.GrpCoord
