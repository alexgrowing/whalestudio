import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupScalarAtFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlaceFrameExistsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.UnitAtLevel

theorem smulOne_mulVec {R : Type} [CommRing R] {n : ℕ} (c : R) (y : Fin n → R) :
    Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y = c • y := by
  funext i
  rw [Matrix.smul_one_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem inv_of_scalar {R : Type} [CommRing R] {n : ℕ} (hn : 0 < n) (A : GL (Fin n) R) (c : R)
    (hA : A.val = c • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ ι : R, ι * c = 1 ∧ (A⁻¹).val = ι • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at h2
  refine ⟨(A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩, by rw [mul_comm]; exact h2, ?_⟩
  have h3 : A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    rw [hA, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, one_smul]
  calc (A⁻¹).val = (A⁻¹).val * (A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R))) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_of_shift {R : Type} [CommRing R] (O : Subring R) (a u ι : R) (ha : ∃ a', a' * a = 1) (hι : ι * u = 1)
    (key : ∀ c, a * c ∈ O ↔ a * (ι * c) ∈ O) : u ∈ O ∧ ι ∈ O := by
  obtain ⟨a', ha'⟩ := ha
  have e1 : a * a' = 1 := by rw [mul_comm]; exact ha'
  have e2 : a * (ι * a') = ι := by linear_combination ι * e1
  have e3 : a * (ι * (a' * u)) = 1 := by linear_combination (ι * u) * e1 + hι
  have e4 : a * (a' * u) = u := by linear_combination u * e1
  constructor
  · have := (key (a' * u)).2 (by rw [e3]; exact O.one_mem)
    rwa [e4] at this
  · have := (key a').1 (by rw [e1]; exact O.one_mem)
    rwa [e2] at this

end GlobalTheory.MiTop.UnitAtLevel

namespace GlobalTheory.MiTop

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem centralRatio_stabLoc_atLevel : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) = v) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by

  intro D L hT Gi Gl Kc Yd cX ex W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hv
  have hm : 0 < D.R.m := by unfold Ranks.rS at hrS; omega
  have hfr := (GlobalTheory.T.self_dual_lattice_frame_chain W hW 0 hm).2
  have hkSt := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) (W.Q.Rl.βY 0) ((pk W).ΛY 0) hfr k).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG hk) v
  obtain ⟨e, α, hl⟩ := GlobalTheory.T.level_place_frame_exists W hW hrS v hv
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.center_adelicUnitaryGroup_scalar_at_finitePlace D (D.sp.Y 0) z hzc v
  have hpos : 0 < (D.sp.Y 0).rank := by
    have := B.d.rank_add
    omega
  obtain ⟨ι, hιζ, hζinv⟩ := GlobalTheory.MiTop.UnitAtLevel.inv_of_scalar hpos _ ζ hζ
  have htinv : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f B a₀ a)))⁻¹ =
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹ *
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f' B' a₀' a')))⁻¹ *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z))⁻¹) := by
    rw [he, map_mul, map_mul, map_mul, map_mul, mul_inv_rev, mul_inv_rev]
  have hkinv : ∀ y, y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v ↔
      Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹).val y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v := by
    have h := GlobalTheory.AdelicU.mem_stabLoc.1 (inv_mem hkSt)
    intro y
    have h2 := h y
    rw [map_inv] at h2
    exact h2
  have key : ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v ↔
      ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * (ι * c) ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
    intro c
    rw [← hl u f B (GlobalTheory.MiTop.PlacedP.placed f B hP) a₀ a hA c, ← hl u' f' B' (GlobalTheory.MiTop.PlacedP.placed f' B' hP') a₀' a' hA' (ι * c), htinv, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hζinv, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec, smul_smul]
    exact (hkinv _).symm
  obtain ⟨hζO, hιO⟩ := GlobalTheory.MiTop.UnitAtLevel.mem_of_shift (GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) _ ζ ι
    ⟨α, Units.mul_inv α⟩ hιζ key
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  intro y
  rw [hζ, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec]
  constructor
  · intro hy
    have := Submodule.smul_mem _ (⟨ζ, hζO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def] at this
  · intro hy
    have := Submodule.smul_mem _ (⟨ι, hιO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def, smul_smul, hιζ, one_smul] at this

end GlobalTheory.MiTop

end
