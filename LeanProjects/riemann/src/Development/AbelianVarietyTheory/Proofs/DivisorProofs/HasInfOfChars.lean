import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Definitions.Foundations.ReferenceTupleNeBaseTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

variable {D : D7}

theorem hasInf_of_chars {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (χ : HChar D.host.E)
    (h : ∀ x, P.W.chV'.f x ^ P.W.ep' = χ.1 (finIdl D x)) :
    χ.HasInf (GlobalTheory.Mem.Chr.embTau D) (fun τ => P.W.ep' * P.W.chV'.n τ) := by
  intro a
  have h1 := χ.2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
  rw [← h (GlobalTheory.NormSum.UnramHecke.incU D a)] at h1
  have h2 := P.W.chV'.aut a
  have h3 : ((χ.inf a : ℂˣ) : ℂ) = (((P.W.chV'.f (GlobalTheory.NormSum.UnramHecke.incU D a) : ℂˣ) : ℂ) ^ P.W.ep')⁻¹ := by
    have := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one, Units.val_zpow_eq_zpow_val] at this
    exact eq_inv_of_mul_eq_one_right this
  have hf := eq_inv_of_mul_eq_one_left h2
  rw [h3, hf, inv_zpow, inv_inv, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]
  rfl

end GlobalTheory.BotWeights

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)

theorem weights_const : GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (δ t0 : ℂ), ∃ n₀ : D.what₂.Tau → ℕ,
      ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → P.n = n₀ := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G i j δ t0 => ?_⟩⟩
  have key : ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
      ((Lc.C.mu0 j / G.ch.chiH (D.R.m - i))⁻¹ : HChar D.host.E).HasInf (GlobalTheory.Mem.Chr.embTau D)
        (fun τ => P.W.ep' * P.W.chV'.n τ) := by
    intro s Q P P' hB k
    have h := hasInf_of_chars P _ hB.chars.2 k
    rw [← h]
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    have hx := GlobalTheory.Mem.Chr.TieModel.inf_eq_one_of_order hn ho k
    have hx' : (Lc.xiH s).inf k = 1 := hx
    simp only [nuH, div_eq_mul_inv, Formalism.L2.Host.HChar.inf_inv, Formalism.L2.Host.HChar.inf_mul, hx', mul_one]
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', h₀⟩ := hex
    refine ⟨P₀.n, fun s Q P P' hB => funext fun τ => ?_⟩
    have e := congrFun (GlobalTheory.Mem.Chr.TieModel.hasInf_unique _ (GlobalTheory.Mem.Chr.TieModel.embTau_inj D)
      (GlobalTheory.Mem.Chr.TieModel.embTau_ne_conj D) (key s Q P P' hB) (key s₀ Q₀ P₀ P₀' h₀)) τ
    have w1 := P.wt τ
    have w2 := P₀.wt τ
    have d1 : (P.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast hB.rank.2.2.1
    have d2 : (P₀.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast h₀.rank.2.2.1
    have : (P.n τ : ℤ) = P₀.n τ := by linarith
    exact_mod_cast this
  · exact ⟨0, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩

end GlobalTheory.BotWeights
