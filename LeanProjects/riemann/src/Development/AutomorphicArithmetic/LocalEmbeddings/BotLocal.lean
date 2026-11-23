import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.BotCoord
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
import Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent
import Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.BotMatch

variable {D : D7}

set_option maxHeartbeats 1600000 in
theorem local_pair {ψ : AddChar (AF D.host.F) ℂ} {W W₁ X : HSp D} {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank} {Xc : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W}
    {om' : Rep D.sp.cm.sig Γ.V' Γ.W} (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc) {R Rf}
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (sW : IsSelfDualC (GlobalTheory.Grid.sgn true W) ΛW) {βW : GL (Fin W.rank) (Lev.EAf D)} (fW : Formalism.L2.DIV.IsFrame βW ΛW)
    (hL : Γ.V.L = GlobalTheory.TripleSpaceW.conjSub ΛW) (βW₁ : GL (Fin W₁.rank) (Lev.EAf D)) (βX : GL (Fin X.rank) (Lev.EAf D))
    {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq (α / β) νH) (i : Bs.P) (hi : i.1 ∈ Xc.T) {c : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt νH (splitPrime (Bs.τ i)) c) :
    ∃ (I : ((Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (I' : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (φ : (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ)
      (φ' : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) (lam : ℂ),
      Γ.M.IsLinW Bs.ψ (Bs.τ i) (Γ.V.bas i) (Γ.W.bas i) I ∧ Γ.M'.IsLinBar Bs.ψ (Bs.τ i) (Γ.V'.bas i) (Γ.W.bas i) I' ∧
      φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ lam ≠ 0 ∧ Rf.p i φ = Rf.p' i φ' ∧
      (∀ x : WO W X, I φ (((Γ.V.bas i)⁻¹).1 * (GlobalTheory.TripleRead.ptO (GlobalTheory.Grid.sgn true W).gram e x).map (piW (Bs.τ i)) *
          ((Γ.W.bas i)⁻¹).1ᵀ) =
        GlobalTheory.StdPairCone.stdA (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          ((((frMapO W X βW βX x).map (evW (Bs.τ i)))ᵀ).submatrix id e)) ∧
      ∀ y : WO W₁ X, I' φ' (-((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) *
          (GlobalTheory.TripleRead.ptO W₁.gram e y).map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1)) =
        lam * GlobalTheory.StdPairCone.stdB (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord W₁ X βW₁ βX y).map (evW (Bs.τ i))).submatrix id e) := by
  have hXν : Xc.ν = α / β := by
    show Xc.α / Xc.β = _
    rw [h.α, h.β]
  obtain ⟨I, I', hI, hI', -, -, hiff⟩ := hM.fin.zeta i hi
  obtain ⟨-, -, hquot, ⟨m, hmα, hmβ⟩, hua, hub⟩ := GlobalTheory.T.seesawCharacter_conductor_at_ramified_place _ _ _ Bs _ _ Γ Xc om om' hM.triple i hi
  obtain ⟨hcond, hc1⟩ := UpperTheory.localChar_conductor_le_of_heckeExponent D (α / β) νH hν i.1 (Bs.τ i) c hc
  have hram := hM.triple.chars.ram (splitPrime (Bs.τ i)) ((splitPrime_under (Bs.τ i)).symm ▸ hi)
  rw [hXν] at hram
  obtain ⟨gA, hgA, egA⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D (GlobalTheory.Grid.sgn true W) ΛW βW sW fW i.1 (Bs.τ i) (Γ.V.bas i)
    (hL ▸ hM.triple.geo.hV.bas i)
  have hx1 : (βX.val.map (evW (Bs.τ i))).submatrix e e * ((βX⁻¹).val.map (evW (Bs.τ i))).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.submatrix_one_equiv]
  let bX : GL (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) := ⟨_, _, hx1, mul_eq_one_comm.1 hx1⟩
  have hy1 : (βW₁⁻¹).val.map (evW (Bs.τ i)) * βW₁.val.map (evW (Bs.τ i)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hy2 := gram_inv_map (Bs.τ i) W₁
  have hy3 : ((Γ.V'.bas i)⁻¹).valᵀ * (Γ.V'.bas i).valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  let gB : GL (Fin W₁.rank) (Fv D.host.F i.1) :=
    ⟨_, _, hy1, mul_eq_one_comm.1 hy1⟩ * ⟨_, _, hy2, mul_eq_one_comm.1 hy2⟩ * ⟨_, _, hy3, mul_eq_one_comm.1 hy3⟩
  rw [← hXν] at hcond ⊢
  obtain ⟨lam, Ξ, Ψ, hlam, eΞ, eΨ, sΞ, sΨ, nΞ, nΨ, hz⟩ := UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate (Fv D.host.F i.1) _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c m
    W.rank W₁.rank (GlobalTheory.SplitFlip.exists_isUnif).choose_spec hquot (hc1 hram) hcond hmα hmβ hua hub gA gB
    ((Γ.W.bas i)⁻¹ * bX) hgA
  obtain ⟨φ, sφ, rfl⟩ := hI.bij.surjOn sΞ
  obtain ⟨φ', sφ', rfl⟩ := hI'.bij.surjOn sΨ
  refine ⟨I, I', φ, φ', lam, hI, hI', sφ, sφ', fun h0 => nΞ (by rw [h0, map_zero]), fun h0 => nΨ (by rw [h0, map_zero]), hlam,
    (hiff φ sφ φ' sφ').2 hz, fun x => ?_, fun y => ?_⟩
  · rw [eΞ, egA]
    exact congrArg _ (frMapO_coX (Bs.τ i) (GlobalTheory.Grid.sgn true W) X e βW βX (Γ.V.bas i) (Γ.W.bas i) x)
  · rw [eΨ, h.JW₁, h.JX]
    exact congrArg (fun z => lam * GlobalTheory.StdPairCone.stdB _ _ c _ _ z)
      (dualCoord_coY (Bs.τ i) W₁ X e βW₁ βX (Γ.V'.bas i) (Γ.W.bas i) y)

end GlobalTheory.BotMatch

end
