import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section
namespace GlobalTheory.OppositeEdges

theorem oppositePath_prod_mulSingle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ) :
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  intro hj κ hκ
  set g : Γ.VertexGroup := Pi.mulSingle (j + 1, Γ.m) κ with hg
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  have hK : ∀ Y, g Y ∈ GlobalTheory.SplitWeil.KO k _ := by
    intro Y
    by_cases hY : Y = (j + 1, Γ.m)
    · subst hY; simpa [hg] using hκ
    · rw [hg, Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z

  have hfar : ∀ b : Edge, b.src ≠ (j + 1, Γ.m) → b.tgt ≠ (j + 1, Γ.m) → Γ.edgeFactor .one g b = 1 := by
    intro b h1 h2
    simp [Grid.edgeFactor, hg, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, hap]
  have htheta : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one g)).prod = 1 := by
    refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  have hex : (((List.range Γ.m).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one g)).prod =
      ∏ i ∈ Finset.range Γ.m, Γ.edgeFactor .one g (.ex i Γ.m) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hne : j ≠ j + 1 := by omega
  have hrest : ∀ i ∈ Finset.range Γ.m, i ≠ j ∧ i ≠ j + 1 → Γ.edgeFactor .one g (.ex i Γ.m) = 1 := by
    intro i _ hi
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  rw [oppositePath, List.map_append, List.prod_append, htheta, mul_one, hex,
    Finset.prod_eq_mul j (j + 1) hne hrest (by simp; omega) (by simp; omega)]
  have hκa : ∀ z : ℂ, apow (gdet (Assignment.one.read κ)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO hκ)) z
  have hj1 : (j + 1 + 1, Γ.m) ≠ (j + 1, Γ.m) := by simp
  have hj0 : (j, Γ.m) ≠ (j + 1, Γ.m) := by simp
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, Pi.mulSingle_eq_of_ne hj1,
    Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_same, hκa, map_one, hap, Units.val_one, inv_one, one_mul]
  simp only [Grid.kappa, Grid.blockChar, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Nat.add_sub_cancel]
  have h1 := Units.ne_zero (Γ.chi (Γ.m - (j + 1)) (gdet κ))
  have h2 := Units.ne_zero (Γ.chi (Γ.m - j) (gdet κ))
  have h3 := Units.ne_zero ((Γ.eta ^ ((Γ.rank (j + 1, Γ.m) + 1) % 2)) (gdet κ))
  field_simp

end GlobalTheory.OppositeEdges
