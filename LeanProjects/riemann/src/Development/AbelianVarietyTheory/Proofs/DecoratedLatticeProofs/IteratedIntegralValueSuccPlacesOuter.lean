import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawPeriodsLinearRelationsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqOfOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem gl₂_comm (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (a : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)
    (b : GL (Q'.n₂ ⊕ Fin (Q'.c + 1)) Q'.k) : Q₀.gl₂ a * Q'.gl₂ b = Q'.gl₂ b * Q₀.gl₂ a := by
  have h0 : Q₀.gl₂ a ∈ grpAt S.B'.V (· = Q₀.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q₀.k Q₀.q S.B'.V _ Q₀.F.G₂ Q₀.gl₂ Q₀.loc₂).2.1]; exact ⟨a, rfl⟩
  have h1 : Q'.gl₂ b ∈ grpAt S.B'.V (· = Q'.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q'.k Q'.q S.B'.V _ Q'.F.G₂ Q'.gl₂ Q'.loc₂).2.1]; exact ⟨b, rfl⟩
  exact GlobalTheory.SeeSawLastValue.grpAt_comm (fun p hp hp' => hne (hp.symm.trans hp')) h0 h1

theorem typed_trc (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (e : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k →₀ ℂ)
    {f : GA D S.B'.V → ℂ} (hf : Q'.Typed f) : Q'.Typed (trc (e.mapDomain Q₀.gl₂) f) := by
  classical
  intro j
  funext x
  have hj := hf j
  simp only [rTrans, Pi.smul_apply, smul_eq_mul, trc_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have := congrFun hj (x * Q₀.gl₂ a)
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at this
  rw [mul_assoc x, ← gl₂_comm Q₀ Q' hne, ← mul_assoc, this]
  ring

theorem away_pair (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) {A T : HSp D} (c d : WO A T →₀ ℂ) (hc : Q'.Away c)
    (hd : ∀ u ∈ d.support, IsHalf (Q₀.q.e + cA D Q₀.q.e) u) : Q'.Away (aconv [c, d]) := by
  obtain ⟨ε₀, hε₀, he₀⟩ := Q₀.q.above
  obtain ⟨ε', hε', he'⟩ := Q'.q.above
  have horth : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε₀ = 0 := by
    rw [← map_mul, GlobalTheory.VacuumFrameCompare.place_orth hε' hε₀ (Ne.symm hne), map_zero]
  intro u hu i j
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_aconv_pair c d hu
  have h1 := hc a ha i j
  have h2 := hd b hb i j
  rw [he'] at h1 ⊢
  rw [he₀] at h2
  have h3 : (1 - algebraMap (AF D.host.F) (AE D) ε') * b i j = b i j := by
    rw [← h2, sub_mul, one_mul, ← mul_assoc, horth, zero_mul, sub_zero]
  rw [Matrix.add_apply, mul_add, h1, h3]

theorem hyps_succ {r : ℕ} (Q : Fin (r + 1) → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ} {f₁ : WO S.B.V S.J.W → ℂ} {f₂ : WO S.J.W S.B'.V → ℂ}
    {φ : GA D S.B.A → ℂ} {f : GA D S.B'.V → ℂ} {g : GA D S.B.V} {h₁ : GA D S.J.W} {h₂ : GA D S.B'.V}
    (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (γ : (Q 0).A₁) (β : (Q 0).A₂) :
    Hyps (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  have hne : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  have hP : ∀ v, places (fun i : Fin r => Q i.succ) v → places Q v := fun v ⟨i, hi⟩ => ⟨i.succ, hi⟩
  refine ⟨fun i => ⟨away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).1 ((Q 0).ent₁ γ).1,
      away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).2 ((Q 0).ent₂ γ β).1⟩, t1, t2, fun i => hv i.succ, hφ,
    contAut_trc _ hf, fun i => typed_trc (Q 0) (Q i.succ) (hne i) _ (ht i.succ),
    grpOff_anti D _ _ _ hP hg, grpOff_anti D _ _ _ hP hh₁, grpOff_anti D _ _ _ hP hh₂⟩

theorem trc_conv_cons {V : HSp D} (E : GA D V →₀ ℂ) (l : List (GA D V →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) (f : GA D V → ℂ) :
    trc (conv (E :: l)) f = trc (conv l) (trc E f) := by
  have e1 : conv (E :: l) =
      (MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ (GA D V)).coeff := by
    rw [← comm_conv E l h, ← conv_cons]
  rw [e1, trc_mul]

theorem sum_pi_succ {r : ℕ} {α : Fin (r + 1) → Type} [∀ i, Fintype (α i)] (F : (∀ i, α i) → ℂ) :
    ∑ γ, F γ = ∑ a : α 0, ∑ γ' : ∀ i : Fin r, α i.succ, F (Fin.cons a γ') := by
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem value_succ {r : ℕ} (Q : Fin (r + 1) → QStep S)
    (hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a)
    (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = ∑ p : (Q 0).A₁ × (Q 0).A₂, (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2) *
      value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
        (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  classical
  have hX : ∀ (γ0 : (Q 0).A₁) (β0 : (Q 0).A₂) (γ' : ∀ i : Fin r, (Q i.succ).A₁) (β' : ∀ i : Fin r, (Q i.succ).A₂),
      S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)))
        (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)
          ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i).e₂ ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i)).mapDomain (Q i).gl₂)) f)
        g h₁ h₂ =
      S.val (aconv (aconv [c₁, (Q 0).d₁ γ0] :: List.ofFn fun i => (Q i.succ).d₁ (γ' i)))
        (aconv (aconv [c₂, (Q 0).d₂ γ0 β0] :: List.ofFn fun i => (Q i.succ).d₂ (γ' i) (β' i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i.succ).e₂ (β' i)).mapDomain (Q i.succ).gl₂))
          (trc (((Q 0).e₂ β0).mapDomain (Q 0).gl₂) f)) g h₁ h₂ := by
    intro γ0 β0 γ' β'
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [aconv_pair_cons, aconv_pair_cons, trc_conv_cons]
    intro x hx e he y hy
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact hcomm i a b
  rw [Fintype.sum_prod_type]
  simp only [value]
  simp only [sum_pi_succ (α := fun i => ↥(Q i).A₁), sum_pi_succ (α := fun i => ↥(Q i).A₂)]
  simp only [hX]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ0 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β0 _ => Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun β' _ => ?_
  ring

theorem outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  intro D r IH ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hinj' : Function.Injective fun i : Fin r => (Q i.succ).q.v := hinj.comp (Fin.succ_injective _)
  have hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a :=
    fun i => gl₂_comm (Q 0) (Q i.succ) fun h => Fin.succ_ne_zero i (hinj h).symm
  have key := GlobalTheory.SeeSaw.VanMany.iteratedQuotientIntegral_finite_linearCombination ρ₁ μ₁ ρ₂ μ₂ (I := (Q 0).A₁ × (Q 0).A₂)
    (fun p => (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2))
    (fun p x y => integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ x.1 y.1)
    (fun p => value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂)
    (fun p => IH ψ hψ σ S (fun i => Q i.succ) hinj' μ₁ ρ₁ μ₂ ρ₂ hN _ _ f₁ f₂ φ _ g h₁ h₂ (hyps_succ Q hinj hH p.1 p.2))
  rw [value_succ Q hcomm]
  convert key using 1
  funext x y
  simp only [innerVal, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

end GlobalTheory.QValOuter
end
