import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Lit

def ConjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ τ : SmIrr (GL (Fin a) (Af E)), IsFinComp π τ → ∀ σ : ℂ ≃+* ℂ,
      ∃ π' : CuspSub E a, (∀ τ', IsFinComp π' τ' → IsConjBy σ τ τ') ∧
        ∀ (t : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (σ.symm.toRingHom.comp t) m → π'.HasInfChar t m

def ConjR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a), π.IsRegAlg → ∀ τ : SmIrr (GL (Fin a) (Af F)), π.IsFinComp τ → ∀ σ : ℂ ≃+* ℂ,
      ∃ π' : TR.CuspSub F a, (∀ τ', π'.IsFinComp τ' → IsConjBy σ τ τ') ∧
        ∀ (t : F →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (σ.symm.toRingHom.comp t)) m →
          π'.HasInfChar (InfinitePlace.mk t) m

def FinExC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ τ, IsFinComp π τ

def FinExR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∃ τ, π.IsFinComp τ

theorem clozelConjC_of (hF : FinExC) (h : ConjC) : Published.ClozelConjC := by
  intro E _ _ _ a ha π hπ σ
  obtain ⟨τ, hτ⟩ := hF E a π
  obtain ⟨π', h1, h2⟩ := h E a ha π hπ τ hτ σ
  obtain ⟨τ', hτ'⟩ := hF E a π'
  refine ⟨π', τ, τ', hτ, hτ', h1 τ' hτ', fun φ m hm => h2 _ m ?_⟩
  convert hm using 1
  exact RingHom.ext fun x => σ.symm_apply_apply _

theorem clozelConjR_of (hF : FinExR) (h : ConjR) : Published.ClozelConjR := by
  intro F _ _ _ a ha π hπ σ
  obtain ⟨τ, hτ⟩ := hF F a π
  obtain ⟨π', h1, h2⟩ := h F a ha π hπ τ hτ σ
  obtain ⟨τ', hτ'⟩ := hF F a π'
  refine ⟨π', τ, τ', hτ, hτ', h1 τ' hτ', fun φ m hm => h2 _ m ?_⟩
  convert hm using 2
  exact RingHom.ext fun x => σ.symm_apply_apply _

end UpperTheory.V.Lit
