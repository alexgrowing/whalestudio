import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

theorem conjChar_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i σ
  refine ⟨fun μ' μ'' h g => eq_of_conj_on_finite (σ := σ) (μ := R.mu0 ((i : ℕ) + 1)) h.1 g.1
    (fun x hx => (h.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩) (fun x hx => (g.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩),
    fun η' η'' h g => GlobalTheory.UnramCharUnique.isEtaConj_unique D σ R.eta η' η'' h g⟩

end GlobalTheory.ConjCharUnique
