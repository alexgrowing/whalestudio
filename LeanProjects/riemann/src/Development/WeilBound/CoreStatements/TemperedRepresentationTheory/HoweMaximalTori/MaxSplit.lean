import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary

noncomputable section

namespace PositivityTheory.HoweDualityUnitaryAlt

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

def KSSub : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (N : ℕ) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) omA omB l, Continuous χ →
    n < m → m < 2 * n → IsSplitPair c ψ JA JB d χ Cy omA omB l →
    ∃ K₀ : Submodule ℂ (UG c JB → ℂ), K₀ ≤ (SB (κ → k)).map (secOf omB l) ∧ K₀ ≠ ⊥ ∧
      (∀ S : Submodule ℂ (UG c JB → ℂ), S ≤ (SB (κ → k)).map (secOf omB l) → (∀ f ∈ S, ∀ h, (fun g => f (g * h)) ∈ S) →
        S ≠ ⊥ → K₀ ≤ S) ∧
      ∀ S : Submodule ℂ (UG c JB → ℂ), K₀ ≤ S → S ≤ (SB (κ → k)).map (secOf omB l) → (∀ f ∈ S, ∀ h, (fun g => f (g * h)) ∈ S) →
        S = K₀ ∨ S = (SB (κ → k)).map (secOf omB l)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def MaxAt {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ N N', Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N' →
    N = N'

def MaxOn (Q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Chars F E → Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, Q F E X v →
      MaxAt om v ∧ MaxAt om' v

def MaxFinT : Prop := MaxOn fun _ _ _ _ _ _ _ _ _ => True

def MaxInert : Prop := MaxOn fun F E _ _ _ _ _ _ v => IsEmpty (E →ₐ[F] Fv F v)

def MaxSplit : Prop := MaxOn fun F E _ _ _ _ _ _ v => Nonempty (E →ₐ[F] Fv F v)

end PositivityTheory.HoweDualityUnitaryAlt

end
