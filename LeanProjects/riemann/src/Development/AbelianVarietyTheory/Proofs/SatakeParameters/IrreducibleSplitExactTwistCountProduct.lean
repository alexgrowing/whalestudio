import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteLStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientProdReorderedCuspSupportStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BlockSplitProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_mul (α β : ℂˣ) : unrChar k (α * β) = unrChar k α * unrChar k β := by
  refine MonoidHom.ext fun x => ?_
  simp [unrChar_apply, mul_zpow]

theorem twist_detRep (n : Type) [Fintype n] [DecidableEq n] (ψ φ : kˣ →* ℂˣ) :
    twist (detRep n ψ) (detChar n φ) = detRep n (ψ * φ) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  simp [detRep, ofChar_apply, twist_apply, mul_comm, mul_left_comm, mul_assoc]

theorem nonempty_equiv_of_cast {n m : ℕ} (h : n = m) (x : Irr k n) (ψ : kˣ →* ℂˣ)
    (e : Nonempty ((h ▸ x : Irr k m).π.Equiv (detRep (Fin m) ψ))) :
    Nonempty (x.π.Equiv (detRep (Fin n) ψ)) := by
  subst h; exact e

theorem eq_one_of_inSupport {m : ℕ} (τ : Irr k m) (hc : IsCuspidal τ.π) {ψ : kˣ →* ℂˣ}
    (h : InSupport τ.π ψ) : m = 1 ∧ Nonempty (τ.π.Equiv (detRep (Fin m) ψ)) := by
  rcases m with _ | _ | m
  · exact absurd h (Model.not_inSupport_zero _ _)
  · obtain ⟨ω, hω, ⟨φ⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ τ.π τ.smooth τ.irr
    have h1 : InSupport (detRep (Fin 1) ω) ψ :=
      JacquetExact.inSupport_of_isSubquotient k _ _ _ τ.π _ ψ ((isSmooth_ofChar_iff _).2 hω.detChar)
        (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) h
    obtain rfl := (Model.inSupport_one_iff ω ψ).1 h1
    exact ⟨rfl, ⟨φ⟩⟩
  · exact absurd h (Model.not_inSupport_of_isCuspidal hc ψ)

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n s : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a))
    (ψ : kˣ →* ℂˣ) (hc : IsCuspSupport π d (fun a => (σ a).π)) (h : InSupport π ψ) :
    ∃ a, d a = 1 ∧ Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) ψ)) := by
  obtain ⟨-, hσ, e, hsub⟩ := hc
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ π _ ψ (isSmooth_parInd _ _) hsub h
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k (Fin s) (fun a => Fin (d a)) (Fin n) e _
    (fun a => (σ a).π) ψ (fun a => (σ a).smooth) (fun a => (σ a).irr) h1
  exact ⟨a, eq_one_of_inSupport (σ a) (hσ a).2.2 ha⟩

theorem reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)),
      IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) →
      (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
        ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) →
      ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t →
      ∃ (π₁ : Irr k r) (π₂ : Irr k t) (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s),
        (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧
        IsCuspSupport π₁.π (fun a => d (ι₁ a)) (fun a => (σ (ι₁ a)).π) ∧
        IsCuspSupport π₂.π (fun b => d (ι₂ b)) (fun b => (σ (ι₂ b)).π) ∧
        IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro hB hG hU k _ _ _ _ r t s π d σ S hc hS1 hlink hr ht
  have hσ := hc.2.1
  obtain ⟨s₁, s₂, ι₁, ι₂, e₁, e₂, V₁, V₂, _, _, _, _, ρ₁, ρ₂, m1, m2, sm1, sm2, ⟨φ₁⟩, ⟨φ₂⟩, hsub⟩ :=
    GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  obtain ⟨π₁, π₂, h1, h2, h3⟩ := GlobalTheory.T.irreducibleSubquotient_parabolicProductTwo_finiteLength hB k r t V₁ V₂ ρ₁ ρ₂ π sm1 sm2
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₁ r (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) e₁).of_equiv φ₁.symm)
    ((GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength hB k s₂ t (fun b => d (ι₂ b)) (fun b => σ (ι₂ b)) e₂).of_equiv φ₂.symm) hsub
  exact ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2,
    ⟨π₁.irr, fun a => hσ (ι₁ a), e₁, h1.trans (IsSubquotient.of_injective φ₁.toIntertwiningMap φ₁.toLinearEquiv.injective)⟩,
    ⟨π₂.irr, fun b => hσ (ι₂ b), e₂, h2.trans (IsSubquotient.of_injective φ₂.toIntertwiningMap φ₂.toLinearEquiv.injective)⟩, h3⟩

end GlobalTheory.BlockSplitProd

open GlobalTheory.BlockSplitProd in
theorem GlobalTheory.BlockSplitProd.main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  intro hB hG hU k _ _ _ _ r t χ π s d σ _ hc hcard
  classical
  let S : Finset (Fin s) := Finset.univ.filter fun a =>
    d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))
  have hS : S.card = t := by
    rw [← hcard, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [S]
  have hS1 : ∀ b ∈ S, d b = 1 := fun b hb => (Finset.mem_filter.1 hb).2.1
  have htot : ∑ a, d a = r + t := by
    obtain ⟨e, -⟩ := hc.2.2
    simpa using Fintype.card_congr e
  have ht : ∑ a ∈ S, d a = t := by
    rw [Finset.sum_congr rfl hS1]
    simp [hS]
  have hr : ∑ a ∈ Sᶜ, d a = r := by
    have := Finset.sum_add_sum_compl S d
    omega
  have hlink : ∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α)))) := by
    intro a b ha hb h α ⟨φ⟩
    obtain ⟨hb1, β, ⟨ψ⟩⟩ := (Finset.mem_filter.1 hb).2
    have e1 : twist (detRep (Fin (d b)) (χ * unrChar k β)) (detChar (Fin (d b)) (unrChar k α)) =
        detRep (Fin (d b)) (χ * unrChar k (β * α)) := by
      rw [twist_detRep, unrChar_mul, mul_assoc]
    have ψ' := LocGL.twistEquiv ψ (detChar (Fin (d b)) (unrChar k α))
    rw [e1] at ψ'
    exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans hb1, β * α,
      nonempty_equiv_of_cast h (σ a) _ ⟨φ.trans ψ'⟩⟩)
  obtain ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2, hc1, hc2, hsub⟩ :=
    reorder hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  have hirr := hU k r t s₁ s₂ π₁ π₂ (fun a => d (ι₁ a)) (fun b => d (ι₂ b)) (fun a => σ (ι₁ a))
    (fun b => σ (ι₂ b)) hc1 hc2 fun a b h α => hlink _ _ (m1 a) (m2 b) h α
  obtain ⟨φ⟩ := IsSubquotient.nonempty_equiv hsub π.irr hirr
  refine ⟨π₁, π₂, ⟨φ.symm⟩, fun α hα => ?_⟩
  obtain ⟨a, ha1, hψ⟩ := exists_eq_of_inSupport hG π₁.π (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) _ hc1 hα
  exact m1 a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha1, α, hψ⟩)

end
