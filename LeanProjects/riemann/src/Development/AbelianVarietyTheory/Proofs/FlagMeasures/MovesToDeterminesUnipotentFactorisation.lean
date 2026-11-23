import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUpUniMul
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameStep

theorem frame_mapLF {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem upUni_of_uni {N : ℕ} {K : Type} [Field K] {A : Matrix (Fin N) (Fin N) K} (h : GlobalTheory.LocOver.Uni A) :
    IsUpUni A := fun i j => ⟨fun hij => h.1 i j hij, fun hij => by subst hij; exact h.2 i⟩

theorem upUni_mul {N : ℕ} {K : Type} [Field K] {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A)
    (hB : IsUpUni B) : IsUpUni (A * B) := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul ..)

theorem unip_tri {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : ∃ A : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧
      ∀ b, n (frame F b) = ∑ a, A a b • frame F a := by
  have hmap : ∀ a, (mapFlag n hn.1 F.fl).fvec a = n (F.fl.fvec a) := by
    intro a
    induction a using Fin.lastCases with
    | last => simp [FlagG.fvec, mapFlag]
    | cast i => simp [FlagG.fvec, mapFlag]
  obtain ⟨A, hA, hc⟩ := GlobalTheory.FlagChange.tri_of_unip F.fl (mapFlag n hn.1 F.fl) n hn.2.1 hn.2.2 hmap
  refine ⟨A, upUni_of_uni hA, fun b => ?_⟩
  rw [← hmap b]
  exact hc b

theorem sum_change {D : D7} (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U A : Formalism.L2.SG.PairVal.MatR D) (hU : ∀ b, g (f b) = ∑ a, U a b • f0 a) (b : Fin (D.R.rS + 1)) :
    g (∑ a, A a b • f a) = ∑ c, (U * A) c b • f0 c := by
  simp only [map_sum, map_smul, hU, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem step : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM t n m ⟨hn, hm, ht⟩
  obtain ⟨hρ, hU, hU', hf, hf'⟩ := hM
  obtain ⟨A, hA, hnA⟩ := unip_tri _ n hn
  obtain ⟨A', hA', hmA'⟩ := unip_tri _ m hm
  have ht0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have ht1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  refine ⟨A, A', hA, hA', hnA, hmA', Subgroup.mul_mem _ hρ hn.1, upUni_mul hU hA, upUni_mul hU' hA', ?_, ?_⟩
  · intro b
    rw [LinearEquiv.mul_apply]
    exact (congrArg ρ (hnA b)).trans (sum_change ρ _ _ U A hf b)
  · intro b
    have h0 : ∀ a, (ρ * t₀.lin) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.mul_apply, ← hf' a]
      show _ = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
      rw [frame_mapLF _ ht0]
    have e1 : frame t.frame b = t.lin (frame (lf D (X.Fu u')) b) := frame_mapLF _ ht1 _ b
    rw [e1, ht]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
    have hinv : ∀ x, n (n⁻¹ x) = x := fun x => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [hinv, hmA' b]
    have := sum_change (ρ * t₀.lin) _ _ U' A' h0 b
    simpa only [LinearEquiv.mul_apply] using this

end GlobalTheory.FrameStep
