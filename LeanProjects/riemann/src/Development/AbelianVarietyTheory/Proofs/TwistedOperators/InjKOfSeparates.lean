import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqAdFormsOfValues

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Period

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem bplusConv_add {φ φ' : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F)
    (h' : BplusConv W M φ' F) :
    BplusConv W M (φ + φ') F ∧ Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F := by
  have e : ∀ x, besInt W (φ + φ') F x = fun n => besInt W φ F x n + besInt W φ' F x n := fun x => funext fun n => by
    simp only [besInt, Pi.add_apply]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (φ + φ') F x n ∂M.νN =
      (∫ n in M.fdN, besInt W φ F x n ∂M.νN) + ∫ n in M.fdN, besInt W φ' F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_add (h.1 x) (h'.1 x)
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).add (h'.1 x)
  · simp only [ei]; exact h.2.add h'.2
  · simp only [Bplus, ei]; exact integral_add h.2 h'.2

theorem bplusConv_smul (c : ℂ) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F) :
    BplusConv W M (c • φ) F ∧ Bplus W M (c • φ) F = c * Bplus W M φ F := by
  have e : ∀ x, besInt W (c • φ) F x = fun n => c * besInt W φ F x n := fun x => funext fun n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (c • φ) F x n ∂M.νN = c * ∫ n in M.fdN, besInt W φ F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_const_mul _ _
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).const_mul c
  · simp only [ei]; exact h.2.const_mul c
  · simp only [Bplus, ei]; exact integral_const_mul _ _

theorem bplusConv_zero (F : Fn G (.grid D.R.m 0)) : BplusConv W M 0 F ∧ Bplus W M 0 F = 0 := by
  have e : ∀ x, besInt W (0 : Fn G (.top 0)) F x = fun _ => 0 := fun x => funext fun n => by simp [besInt]
  refine ⟨⟨fun x => by rw [e x]; exact integrableOn_zero, ?_⟩, ?_⟩
  · simp only [e, integral_zero]; exact integrableOn_zero
  · simp only [Bplus, e, integral_zero]

end Period

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1000000 in

theorem inj_of_separates {ch : Choice R} (hIs : ch.Is) (hM : R.IsModels) {ρ : ch.G.RealVec}
    {ξ : Module.Dual ℂ (coefPlus ch.G ch.W.θ).W} (hsep : Separates R ch.W ch.M ch.w ρ ξ)
    (hconv : ∀ a u, ConvK (ch.withReal ρ ξ) a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  have hu' : ∀ a, psiK (ch.withReal ρ ξ) a u = 0 := fun a => hIs.real u hu ρ ξ a
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu' a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2

theorem injK_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate)
    (hL : GlobalTheory.RowClaim.Big fun ch => ∀ ρ ξ a u, ConvK (ch.withReal ρ ξ) a u) : GlobalTheory.RowClaim.InjK := by
  obtain ⟨C1, hL⟩ := hL
  refine ⟨max 6510 C1, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc u hu => ?_⟩
  have hconv := hL D large₂ hε (le_of_max_le_right hx) Γ Pl0 T A Ks R F hset ch hch hsc
  obtain ⟨sc, G, W, M, ρ0, ξ0, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨ρ, ξ, hsep⟩ := hS D large₂ hε (le_of_max_le_left hx) hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W
    hch.weil M hch.vol _ hch.w_ne
  exact inj_of_separates hch hset.core.models hsep (hconv ρ ξ) u hu

end GlobalTheory.RowTest

end
