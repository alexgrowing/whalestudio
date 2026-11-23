import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSecondModelStabilizerIffCarriesRowLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedStabilizerConjSatisfiesDeepCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevRow

open GlobalTheory.FinPl.OrbitCoset in

theorem embA_mem_grpAt {D : D7} {S S₀ A B : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A B) (P : GlobalTheory.FinPl.Pl D → Prop)
    {a : GA D A} (ha : a ∈ grpAt A P) : embA d o a ∈ grpAt S P :=
  wittCoreEmbedding_mem_supportedSubgroup d P (emb_mem_grpAt' o ha)

theorem levrow : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ v : GlobalTheory.FinPl.Pl D, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∃ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 ∧ ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o (a₀ * a * a₀⁻¹)) (latS D) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hE hLev hAd hH v hv a ha
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl a
  refine ⟨y, hy.symm, ?_⟩
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D X h u ψ B F tr hE hAd (a₀ * a * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH.2
  have hh0 : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ := by rw [e0, hh0, one_mul]
      _ = _ := by rw [mul_assoc, h1, mul_one]
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * a * a₀⁻¹) =
      ((tr.h0 * y * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA ((B.toH (a₀ * a * a₀⁻¹)).2 : X.B.I.Gf) (tr.h0 * y * tr.h0⁻¹) := by
    have h' := hRep
    rw [hfg] at h'
    exact h'
  obtain ⟨hmemIff, -⟩ := hLev.2 (B.toH (a₀ * a * a₀⁻¹)).2 _ hRF
  have hconj : tr.h0⁻¹ * (tr.h0 * y * tr.h0⁻¹) * tr.h0 = y := by group
  rw [hconj] at hmemIff
  rw [← hmemIff]
  have hk : a₀ * a * a₀⁻¹ ∈ grpAt (D.sp.X 0) (· = v) :=
    by
      have hN : (grpAt (D.sp.X 0) (· = v)).Normal := by unfold grpAt GlobalTheory.FinPl.congGrp; infer_instance
      exact hN.conj_mem a ha a₀
  have hκ : embA B.d B.o (a₀ * a * a₀⁻¹) ∈ grpAt (D.sp.Y 0) (· = v) := embA_mem_grpAt B.d B.o _ hk
  have hKs := GlobalTheory.T.mem_secondModelStabilizer_iff_carriesRowLattice X h v _ hκ
  change (X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u ∈ X.K2 ↔ _
  rw [← hKs]
  constructor
  · intro h2
    have h3 : (X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u ∈ X.B.I.Kset := h2.1
    have h4 := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (X.xu_K u) h3)
      (Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I (X.xu_K u))
    have e : X.xu u * ((X.xu u)⁻¹ * (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 * X.xu u) * (X.xu u)⁻¹ =
        (iotaX X h (embA B.d B.o (a₀ * a * a₀⁻¹))).2 := by group
    rw [e] at h4
    exact h4
  · intro h2
    refine ⟨?_, GlobalTheory.T.supportedStabilizer_conj_satisfies_deepCongruence X h u v hv _ hκ h2⟩
    exact Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I
      (Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I (X.xu_K u)) h2) (X.xu_K u)

end GlobalTheory.Core.Mi.LevRow

end
