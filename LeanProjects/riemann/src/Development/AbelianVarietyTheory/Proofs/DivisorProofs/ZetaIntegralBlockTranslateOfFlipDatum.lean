import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDepthSplitThetaBigEqSmallBlockTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleSquareSplitPlaceCharacterEqLocalGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach in

theorem GlobalTheory.PureMatch.pure_match : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P),
    ∀ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v), ∀ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
    ∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
    ∀ s : GL (Fin (spV G i j).rank) (Fv D.host.F v) → GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) → ℂ, (∀ K₁ K₂, s K₁ K₂ ≠ 0) →
    ∃ n Φ K₁ K₂, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      bigP (haarVol (KO _ (Fin (spW G i j).rank))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩))
          (fun Z => s K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
            (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1))) =
        smallP (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hM hT w hw v hv hP g₀ c₀ Ψ hΨ s hs
  have hτ : splitPrime (Bs.τ ⟨v, hP⟩) = w := hT.2.2.2 ⟨v, hP⟩ w hw hv
  have hb : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hmem
    apply hst.2 w hw
    have hd : GlobalTheory.HalfCompare.badInt D ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK :=
      ⟨D.host.d, by unfold GlobalTheory.HalfCompare.badInt; ring⟩
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hψ := Good.hasConductor_psiAt W hb
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  obtain ⟨hν, hα⟩ := GlobalTheory.T.thetaTripleSquare_splitPlace_character_eq_localGrid hL W M t i j e Bs Γ X h w v hv (Bs.τ ⟨v, hP⟩) hτ
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_depth_splitThetaBig_eq_small_blockTranslate (Fv D.host.F v) (spW G i j).rank (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank))
    (haarVol (KO _ (Fin (spW₁ G i j).rank))) finSumFinEquiv (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩))
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.β (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (blockV e) g₀ c₀ Ψ hΨ hϖv
  obtain ⟨μ, hμ, σ', hphi, hdep⟩ := GlobalTheory.T.datumPhiA_splitPlace_transport_eq hL t i j e w hw v hv (Bs.τ ⟨v, hP⟩) hτ (max (2 * m) (depthAt G w))
  let K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v) := diagGL fun _ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
  let K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v) := diagGL fun _ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹
  obtain ⟨Ξ, hΞ, heq⟩ := hm _ (le_max_left _ _) μ σ' (s K₁ K₂) (hs K₁ K₂)
  obtain ⟨Ξ', hΞ', hΞΞ'⟩ := hdep Ξ hΞ
  refine ⟨max (2 * m) (depthAt G w), invFourierSum (psiAt W w) (unifAt w) (max (2 * m) (depthAt G w))
    (Assignment.one.block _ _) Ξ', K₁, K₂, le_max_right _ _,
    FourierDepth.isNatDatum_invFourierSum (isUnif_unifAt w) hψ _ _ hΞ', ?_⟩
  have hsq : ∀ Z, sqCore W t i j w (max (2 * m) (depthAt G w)) (invFourierSum (psiAt W w) (unifAt w)
      (max (2 * m) (depthAt G w)) (Assignment.one.block _ _) Ξ') (trA t hv e Z) =
      phiA μ σ' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.ν (Bs.τ ⟨v, hP⟩)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w))
        (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (max (2 * m) (depthAt G w)) (blockV e)) Ξ Z := by
    intro Z
    unfold sqCore
    rw [GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum _ _ _ _ _ _ _ (isUnif_unifAt w) hψ _ hΞ', hphi, hν]
    congr 1
    exact funext hΞΞ'
  have hblk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 = (diagGL (fun col => if col ∈ blockV e then GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m
      else (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ m)⁻¹)).val := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, K₁, K₂, diagGL_val, blockV, diagonal_apply]
  rw [hα, ← heq]
  congr 1
  funext Z
  rw [Matrix.mul_assoc _ c₀.1, hblk, ← Units.val_mul, hsq]
