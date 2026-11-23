import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleRealizationSquareClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralBlockTranslateOfFlipDatumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

theorem GlobalTheory.SquareFlipReach.flip_reach_of (G1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P) ιA,
      Γ.M.IsLinW Bs.ψ (Bs.τ ⟨v, hP⟩) (Γ.V.bas v) (Γ.W.bas v) ιA →
    ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∃ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v),
    ∃ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
      (∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ → ∃ φ ∈ GlobalTheory.WeilM.SB _, ι φ = flipAt W t i j w n Φ ∧
        ∀ Z, ιA φ Z = c * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1))) ∧
      ∀ (K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v)) (K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v)),
        ∃ g, ∃ c' : ℂ, c' ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∃ φ₃ ∈ GlobalTheory.WeilM.SB _,
          Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ φ₃ ∧
          ∀ Z, ιA φ₃ Z = c' * ιA φ (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1))) (G2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
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
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW X.α (Bs.τ ⟨v, hP⟩)) Ψ) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev φ₀ hφ₀
  have hvT : v ∈ X.T := (hti.2.2.1 v).2 ⟨w, hw, ev⟩
  have hP : v ∈ Bs.P := hm.triple.chars.sub hvT
  obtain ⟨ιA, ιB, hA, hB, -, -, hiff⟩ := hm.fin.zeta ⟨v, hP⟩ hvT
  obtain ⟨φ', hφ', e'⟩ : Rf.p v φ₀ ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
  have hΨ : ιB φ' ∈ GlobalTheory.WeilM.SB _ := hB.bij.mapsTo hφ'
  obtain ⟨ι, hι, c, hc, g₀, c₀, hcmp, htr⟩ := G1 hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev hP ιA hA
  choose gK cK hcK hK using htr
  obtain ⟨n, Φ, K₁, K₂, hn, hΦ, hbig⟩ := G2 hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ev hP g₀ c₀ (ιB φ') hΨ
    (fun K₁ K₂ => c * cK K₁ K₂) (fun K₁ K₂ => mul_ne_zero hc (hcK K₁ K₂))
  obtain ⟨φ₂, hφ₂, hιφ₂, hc₂⟩ := hcmp n Φ hn hΦ
  obtain ⟨φ₃, hφ₃, hact, hc₃⟩ := hK K₁ K₂ φ₂ hφ₂
  refine ⟨n, Φ, φ₂, gK K₁ K₂, φ₃, hn, hΦ, ⟨hφ₂, ι, hι, hιφ₂⟩, hφ₃, hact, ?_⟩
  have e1 : ιA φ₃ = fun Z => c * cK K₁ K₂ * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ
      (GlobalTheory.SquareFlipReach.trA t ev e (g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1)) := by
    funext Z
    rw [hc₃, hc₂]
    have e2 : g₀.1 * (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1)) * c₀.1 =
        g₀.1 * Z * c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 := by
      simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [e2, mul_comm c (cK K₁ K₂), mul_assoc]
  have e3 := (hiff φ₃ hφ₃ φ' hφ').2 (by rw [e1]; exact hbig)
  exact e3.trans e'

theorem GlobalTheory.SquareFlipReach.flip_reach : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v, w.under (𝓞 D.host.F) = v → ∀ φ₀ ∈ GlobalTheory.WeilM.SB _,
    ∃ n Φ φ₂ g φ₃, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧ IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) φ₂ ∧
      φ₃ ∈ GlobalTheory.WeilM.SB _ ∧ Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀ :=
  GlobalTheory.SquareFlipReach.flip_reach_of GlobalTheory.T.theta_triple_realization_square_class GlobalTheory.T.zetaIntegral_block_translate_of_flip_datum
