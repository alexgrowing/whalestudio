import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLatticeStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CentralUnitGen

theorem scalar_keeps {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (Λ : Submodule S (Fin n → R)) (w : Fin n → R)
    (Mt Mt' Mk Mki : Matrix (Fin n) (Fin n) R) (c c' : R)
    (h1 : Mt = (c • (1 : Matrix (Fin n) (Fin n) R)) * Mt' * Mk) (h2 : (c' * c) • (1 : Matrix (Fin n) (Fin n) R) = 1)
    (hkk : Mk * Mki = 1)
    (hk : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mk y ∈ Λ) (hki : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mki y ∈ Λ)
    (hw : ∀ c0 : R, ((∃ x ∈ Λ, Matrix.mulVec Mt x = c0 • w) ↔ c0 ∈ S) ∧ ((∃ x ∈ Λ, Matrix.mulVec Mt' x = c0 • w) ↔ c0 ∈ S)) :
    ∀ y, y ∈ Λ ↔ Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y ∈ Λ := by
  have e2 : Mt' * Mk = (c' • (1 : Matrix (Fin n) (Fin n) R)) * Mt := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, Matrix.one_mul]
  have hcI : c ∈ S := by
    obtain ⟨x', hx', ex'⟩ := ((hw 1).2).2 (one_mem _)
    refine ((hw c).1).1 ⟨Matrix.mulVec Mki x', (hki x').1 hx', ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.mul_assoc, Matrix.mul_assoc, hkk, Matrix.mul_one, ← Matrix.mulVec_mulVec, ex', one_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc'I : c' ∈ S := by
    obtain ⟨x, hx, ex⟩ := ((hw 1).1).2 (one_mem _)
    refine ((hw c').2).1 ⟨Matrix.mulVec Mk x, (hk x).1 hx, ?_⟩
    rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec, ex, one_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro y
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hy
    exact Λ.smul_mem ⟨c, hcI⟩ hy
  · intro hy
    have h3 := Λ.smul_mem ⟨c', hc'I⟩ hy
    have e3 : (c' * c) • y = y := by
      have := congrArg (fun A => Matrix.mulVec A y) h2
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using this
    rw [← e3, mul_smul]
    exact h3

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.CentralUnitGen

theorem proj_mem_center {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : GlobalTheory.AdelicU.GAd σ J}
    (hg : g ∈ Subgroup.center (GlobalTheory.AdelicU.GAd σ J)) : GlobalTheory.AdelicU.proj σ J v g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc σ J v) := by
  refine Subgroup.mem_center_iff.2 fun x => ?_
  have e := congrArg (GlobalTheory.AdelicU.proj σ J v) (Subgroup.mem_center_iff.1 hg (GlobalTheory.AdelicU.emb σ J v x))
  rwa [map_mul, map_mul, GlobalTheory.AdelicU.proj_emb_self] at e

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem centralRatio_unit_gen : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTu hTu'
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hfr := (GlobalTheory.Fam.sdY_frames W hP 0 hm).2
  have hkS : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((pk W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkv := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ ((pk W).ΛY 0) hfr k).1 hkS v
  have hkv' := Subgroup.inv_mem _ hkv
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v hzc)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v (Subgroup.inv_mem _ hzc))
  obtain ⟨w, hw⟩ := GlobalTheory.T.placed_bessel_pair_lattice W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' v hv hTu hTu'
  have h2 : (c' * c) • (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
    have h := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) (inv_mul_cancel z)
    simp only [map_mul, map_one, Units.val_mul, Units.val_one] at h
    rw [hc, hc', Matrix.smul_mul, Matrix.one_mul, smul_smul] at h
    exact h
  have h1 := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) he
  simp only [map_mul, Units.val_mul] at h1
  rw [hc] at h1
  have hkk : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)).1 *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  rw [hc]
  exact GlobalTheory.CentralUnitGen.scalar_keeps _ w _ _ _ _ c c' h1 h2 hkk (GlobalTheory.AdelicU.mem_stabLoc.1 hkv)
    (GlobalTheory.AdelicU.mem_stabLoc.1 hkv') hw

end GlobalTheory.MiTop

end
