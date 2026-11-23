import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep.IdempotentCombination

variable {D : D7}

section Idem
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finset_sum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

end GlobalTheory.TriStep.IdempotentCombination

namespace GlobalTheory.TriStep

theorem aconv_single_list {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  show d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b)) = d
  calc d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b))
        = d.sum (fun g a => Finsupp.single g a) := by
          congr 1; funext g a; rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    _ = d := Finsupp.sum_single d

theorem comb_aconv_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {A T : HSp D}
    (c d : WO A T →₀ ℂ) (hc : Q.Away c)
    (hd : ∀ u ∈ d.support, IsHalf ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) u) (g : WO A T → ℂ) :
    comb ψ A T (aconv [c, d]) g = comb ψ A T c (comb ψ A T d g) := by
  rw [GlobalTheory.TriStep.IdempotentCombination.comb_aconv_cons c [d] ?_ g, aconv_single_list]
  intro x hx y hy
  rw [aconv_single_list] at hy
  have hy' : IsHalf (Q.q.e + cA D Q.q.e) y := hd y hy
  refine GlobalTheory.HeisComb.symplO_half A T (1 - (Q.q.e + cA D Q.q.e)) (Q.q.e + cA D Q.q.e) x y ?_ ?_ (hc x hx) hy'
  · rw [map_sub, map_one, GlobalTheory.TriStep.IdempotentCombination.cA_idem]
  · rw [sub_mul, one_mul, GlobalTheory.TriStep.IdempotentCombination.idem_sq, sub_self]

theorem valK_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hcon Ξ₁ Ξ₂ d₁ d₂ hd₁ hd₂ O₁ O₂ hO₁ hO₂ f hf
  have hσc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol
  let P₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let P₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₁ : SB (Matrix Q.n₁ Q.n₀ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₂ : SB (Matrix Q.n₂ Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have e₁ : flatBF S.s₁ (T₁ O₁) = U₁ P₁ := hU₁ O₁ P₁ (by
    rw [hO₁, (hun Q.n₁ Q.n₀ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)])
  have e₂ : flatFB S.s₂ (T₂ O₂) = U₂ P₂ := hU₂ O₂ P₂ (by
    rw [hO₂, (hun Q.n₂ Q.n₁ Q.n₀ (Q.c + 1) (σ + 1)).2.1 (by omega) (by omega)])
  obtain ⟨ΞO, hΞO, eΛ⟩ := hcon P₁ P₂
  have hΞO' : ∀ q, ΞO.1 q = R₁.1 q.1 * R₂.1 q.2 := fun q => by
    rw [hΞO]; exact (hun Q.n₁ Q.n₀ Q.n₂ 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) ψ Q.n₁ Q.n₀ Q.n₂).1 S.B.A S.J.W₀ S.B'.A
    Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ d₁ d₂ Ξ₁ R₁ Ξ₂ R₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) ΞO hΛ hd₁ hd₂ rfl rfl (fun q => rfl) hΞO'
  have hbc := GlobalTheory.ProdLocInv.biComb_comp ψ S.B.A S.J.W₀ S.B'.A c₁ d₁ (aconv [c₁, d₁]) c₂ d₂ (aconv [c₂, d₂])
    (comb_aconv_away Q c₁ d₁ hc₁ hd₁.1) (comb_aconv_away Q c₂ d₂ hc₂ hd₂.1) (Λ ΞO)
  have hom₁ : S.s₁.om (1, 1) = 1 := map_one _
  have hom₂ : S.s₂.om (1, 1) = 1 := map_one _
  simp only [GlobalTheory.TriStep.valK, Dbl2.val, Dbl2.con, GlobalTheory.TriStep.rTrans_one]
  rw [hom₁, hom₂, Module.End.one_apply, Module.End.one_apply, e₁, e₂, eΛ, ← hbc, hbi]

end GlobalTheory.TriStep
