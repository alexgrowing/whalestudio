import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTupleStatement

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.SqTop.BotT

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem nuH_eq (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    nuH G t i j = nuH G μ₀ i j * L.xiH t := by
  simp only [nuH, hL.xi_base, mul_one]
  exact mul_div_right_comm _ _ _

theorem alphaH_eq (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    alphaH L t i j = alphaH L μ₀ i j * L.xiH t := by
  simp only [alphaH, hL.xi_base, mul_one]
  exact mul_right_comm _ _ _

theorem exists_heckeU_nuInv (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) ∧
      ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  obtain ⟨χ₀, h₀, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨ξ, hξ, hn⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ (GlobalTheory.AlphaSplit.invU ξ) (by simp), fun x => ?_, fun τ => ?_⟩
  · rw [GlobalTheory.AlphaSplit.mulU_f, GlobalTheory.AlphaSplit.invU_f, h₀, hξ, nuH_eq hL G t, mul_inv]
    rfl
  · show _ ≤ χ₀.n τ + -ξ.n τ
    rw [hn, neg_zero, add_zero]; exact hw τ

theorem exists_heckeU_alpha (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botSmall D i j), ∀ x, χ.f x = (alphaH L t i j).1 (finIdl D x) := by
  obtain ⟨χ₀, h₀⟩ := GlobalTheory.FunObj.SqNum.exists_heckeU_alphaH hL G i j
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ ξ (by simp), fun x => ?_⟩
  rw [GlobalTheory.AlphaSplit.mulU_f, h₀, hξ, alphaH_eq hL t]
  rfl

theorem pde_ne_q {large₂ : Formalism.BasicNotions.SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

end GlobalTheory.SqTop.BotT

namespace GlobalTheory.SqTop

theorem botExT_holds (hI : ∀ D, GlobalTheory.NormSum.Inp D) : BotExT := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 Q P t i j
  obtain ⟨hq, hq'⟩ := BotT.pde_ne_q hR
  obtain ⟨χν, hν, hw⟩ := BotT.exists_heckeU_nuInv hL G t i j
  obtain ⟨χβ, hβ⟩ := GlobalTheory.FunObj.SqNum.exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := BotT.exists_heckeU_alpha hL G t i j
  obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χβ hβ χν hν hw
  obtain ⟨P₂, h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χα hα χν hν hw
  exact ⟨P₁, P₂, ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

example : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := botExT_holds

end GlobalTheory.SqTop

end
