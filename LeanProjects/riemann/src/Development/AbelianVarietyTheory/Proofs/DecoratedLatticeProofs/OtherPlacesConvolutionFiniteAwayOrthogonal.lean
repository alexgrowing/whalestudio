import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdemMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

namespace GlobalTheory.QVal.InnerSupp

variable {D : D7}

theorem placeIdem_self {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hαα : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α) = evalV D.host.F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α) = ((0 : Ainf D.host.F), α)
  rw [Prod.mk_mul_mk, mul_zero, hαα]

theorem idem_sq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [heq, ← map_mul, placeIdem_self hε]

theorem support_aconv {G : Type} [AddMonoid G] (P : G → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) :
    ∀ l : List (G →₀ ℂ), (∀ c ∈ l, ∀ u ∈ c.support, P u) → ∀ u ∈ (aconv l).support, P u := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ u hu
    have h := Finsupp.support_single_subset (show u ∈ (Finsupp.single (0 : G) (1 : ℂ)).support from hu)
    rw [Finset.mem_singleton] at h
    subst h
    exact h0
  | cons e l ih =>
    intro hl u hu
    have hu' : u ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support := hu
    have h1 := Finsupp.support_sum hu'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g, hg, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨h, hh, h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    subst h5
    exact hadd g h (hl e (List.mem_cons.2 (Or.inl rfl)) g hg)
      (ih (fun c hc => hl c (List.mem_cons.2 (Or.inr hc))) h hh)

theorem side {A T : HSp D} (E₀ : AE D) (hc : cA D E₀ = E₀) (hsq : E₀ * E₀ = E₀) (c₀ : WO A T →₀ ℂ)
    (l : List (WO A T →₀ ℂ)) (h₀ : ∀ x ∈ c₀.support, IsHalf E₀ x)
    (hl : ∀ c ∈ l, ∀ u ∈ c.support, (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0) :
    IsFinComb (aconv l) ∧ (∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u) ∧
      ∀ x ∈ c₀.support, ∀ y ∈ (aconv l).support, symplO A T x y = 0 := by
  have key := support_aconv (fun u : WO A T => (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0)
    ⟨fun a b => by rw [Matrix.zero_apply, mul_zero], by ext a b; simp⟩
    (fun u u' hu hu' => ⟨fun a b => by rw [Matrix.add_apply, mul_add, hu.1 a b, hu'.1 a b, add_zero], by
      ext a b
      have e1 := congrFun (congrFun hu.2 a) b
      have e2 := congrFun (congrFun hu'.2 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.add_apply] at e1 e2 ⊢
      rw [(infPart D).map_add, e1, e2, add_zero]⟩) l hl
  have half : ∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u := fun u hu a b => by
    rw [sub_mul, one_mul, (key u hu).1 a b, sub_zero]
  refine ⟨fun u hu => (key u hu).2, half, fun x hx y hy => ?_⟩
  exact GlobalTheory.HeisComb.symplO_half A T E₀ (1 - E₀) x y hc (by rw [mul_sub, mul_one, hsq, sub_self]) (h₀ x hx) (half y hy)

end GlobalTheory.QVal.InnerSupp

open GlobalTheory.QVal.InnerSupp in

theorem GlobalTheory.QVal.inner_supp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  intro D ψ σ S r Q hinj
  have hv : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  obtain ⟨hc, -, horth⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q 0).k (Q 0).q
  have hsq := idem_sq (Q 0).q
  have kill : ∀ (i : Fin r) {m n : ℕ} (u : Mx D m n), IsHalf ((Q i.succ).q.e + cA D (Q i.succ).q.e) u →
      (∀ a b, ((Q 0).q.e + cA D (Q 0).q.e) * u a b = 0) ∧ u.map (infPart D) = 0 := by
    intro i m n u hu
    obtain ⟨-, hinf, -⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q i.succ).k (Q i.succ).q
    refine ⟨fun a b => ?_, (hinf (fun _ => True) trivial m n u hu).2⟩
    rw [← hu a b, ← mul_assoc, horth (Q i.succ).k (Q i.succ).q (hv i), zero_mul]
  refine ⟨side _ hc hsq (Q 0).D₁ _ (fun x hx => (Q 0).dat₁.1 x hx) ?_, side _ hc hsq (Q 0).D₂ _ (fun x hx => (Q 0).dat₂.1 x hx) ?_⟩
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₁.1 u hu)
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₂.1 u hu)

end
