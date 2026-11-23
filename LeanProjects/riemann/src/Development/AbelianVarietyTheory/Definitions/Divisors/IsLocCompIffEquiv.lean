import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

theorem SoleTerm.mono {ι : Type} {C : ι → ℂ} {p q p' q' : ι → Prop} (h : SoleTerm C p q) (hp : ∀ i, p i → p' i)
    (hq : ∀ i, q' i → q i) : SoleTerm C p' q' := by
  obtain ⟨i, h0, h1, hu⟩ := h
  exact ⟨i, h0, hp i h1, fun j hj hj' => hu j hj (hq j hj')⟩

example : ¬ SoleTerm (![1, -1] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) := by
  rintro ⟨i, -, -, hu⟩
  exact absurd ((hu 0 (by simp) trivial).trans (hu 1 (by simp) trivial).symm) (by decide)

example : SoleTerm (![2, 0] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) :=
  ⟨0, by simp, trivial, fun i hi _ => by fin_cases i <;> simp_all⟩

example : SoleTerm (![2, -2] : Fin 2 → ℂ) (· = 0) (· = 0) := ⟨0, by simp, rfl, fun _ _ h => h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def TraceIdC (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (geo : Set (Pl E) → (InfinitePlace E → DomWeight n) → (∀ w : Pl E, GLw n w → ℂ) → ℂ) : Prop :=
  ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (GLw n w)),
    IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' →
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → Term E n) (C : ι → ℂ), (∀ i, (t i).HasWt lam) ∧
      (∀ φ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → (∃ w ∈ S, RegAt n w (φ w)) → geo S lam φ = spec S t C K' φ) ∧
      (∀ ρc : CuspSub E n, ρc.IsCsd → (∀ v : InfinitePlace E, ρc.HasInfChar v.embedding (infOfWeight (lam v))) →
        (∀ w ∈ S, ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed τ.ρ (K' w) ≠ ⊥) →
        SoleTerm C (fun i => ∀ w, ρc.IsLocComp w ((t i).P w)) (fun i => ∀ w ∈ S, ρc.IsLocComp w ((t i).P w)))

def STFC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n, TraceIdC E n geomSt

def MainIdC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
      (K₁ : ∀ (w : Pl E) a, Subgroup (GLw a w)) (K₂ : ∀ (w : Pl E) a, Subgroup (GLw (n - a) w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ a ≤ n, IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) (K₁ · a) ∧
      IsLevelFam (thL (n - a)) (fun w : Pl E => GlobalTheory.LFun.KGL w (n - a)) (K₂ · a)) →
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → PairTerm E n μ) (C : ι → ℂ), (∀ j, (T j).D.HasWt lam) ∧
      (∀ ρc : CuspSub E n, ρc.IsCsd → (∀ v : InfinitePlace E, ρc.HasInfChar v.embedding (infOfWeight (lam v))) →
        (∀ w ∈ S, IsSplitAt w → ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
        (∀ w ∈ S, ¬ IsSplitAt w → ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed τ.ρ (K₁ w n) ≠ ⊥) →
        SoleTerm C (fun j => (T j).a = n ∧ ∀ w, ρc.IsLocComp w ((T j).D.P w))
          (fun j => ∀ᶠ w in cofinite, w ∈ S → IsSplitAt w → ρc.IsLocComp w ((T j).D.P w))) ∧
      ∀ (f : ∀ w : Pl E, UL n w → ℂ) (φ : ∀ (w : Pl E) a, GLw a w × GLw (n - a) w → ℂ), IsTest (KL n) K' f →
        (∀ a ≤ n, (∀ w, ¬ IsSplitAt w → IsHecke ((K₁ w a).prod (K₂ w a)) (φ w a) ∧ Match n a (n - a) w 1 (f w) (φ w a)) ∧
          ∀ᶠ w in cofinite, ¬ IsSplitAt w →
            φ w a = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) : Subgroup _) : Set _).indicator 1) →
        (∃ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) ∧
          (¬ IsSplitAt w → ∀ a ≤ n, RegAt2 a (n - a) w (φ w a))) →
        geomU S lam f = ∑ j, C j * ∏ᶠ w ∈ S, (T j).fac w (K' w) (f w) (K₁ w) (K₂ w) (φ w)

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
