import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientExtTensorRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_prod₂_equiv {r t : ℕ} {U W A B C D : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U} {ρ : Representation ℂ (GL (Fin t) k) W}
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin (r + t)) k) C} {δ : Representation ℂ (GL (Fin (r + t)) k) D}
    (hα : IsSmooth α) (hβ : IsSmooth β) (h₁ : IsSubquotient σ α) (h₂ : IsSubquotient ρ β)
    (E : (prod₂ σ ρ).Equiv δ) (F : (prod₂ α β).Equiv γ) : IsSubquotient δ γ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans
    ((GlobalTheory.CompanionTheory.ProdSubquot.prod₂_isSubquotient k r t U A W B σ α ρ β hα hβ h₁ h₂).trans
      (.of_injective F.toIntertwiningMap F.toLinearEquiv.injective))

theorem nonempty_prod₂_equiv_prodIrr_succ {c : ℕ} (y : Fin (c + 1) → IrrGL k)
    (hd : ∑ a, (y a).1 = (y 0).1 + ∑ a : Fin c, (y a.succ).1) :
    Nonempty ((prod₂ (y 0).rep (prodIrr (fun a : Fin c => y a.succ) rfl)).Equiv (prodIrr y hd)) := by
  have := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) (fun a => (y a).1) hd fun a => (y a).rep
  exact this

end GlobalTheory.CompanionTheory.Ysupp
