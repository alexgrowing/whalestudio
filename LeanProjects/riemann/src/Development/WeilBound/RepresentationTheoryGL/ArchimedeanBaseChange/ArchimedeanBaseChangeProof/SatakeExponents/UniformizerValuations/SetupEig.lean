import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig

def diagOp {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (Matrix.diagonal fun j => c (blk j)))

def UModel : Prop := ∀ (ι B : Type) [Fintype ι] [Fintype B] (X : ι → B → Type) [∀ i w, AddCommGroup (X i w)]
  [∀ i w, Module ℂ (X i w)] [∀ i w, FiniteDimensional ℂ (X i w)] (L : ∀ i w, Module.End ℂ (X i w)),
  ∃ (d : ℕ) (blk : Fin d → ι) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)),
    (∀ c, Commute u (diagOp blk c)) ∧
    (∀ (c : ι → ℂ) (k : ℕ), LinearMap.trace ℂ _ ((u ^ k * diagOp blk c : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
      EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = ∑ i, c i * ∏ w, LinearMap.trace ℂ _ (L i w ^ k)) ∧
    ∀ i₀, (∀ w, ∃ y, y ≠ 0 ∧ L i₀ w y = y) → ∃ v, v ≠ 0 ∧ u v = v ∧ ∀ c, diagOp blk c v = c i₀ • v

def DiagAlg : Prop := ∀ (ι : Type) (d : ℕ) (blk : Fin d → ι) (c c' : ι → ℂ) (z : ℂ),
  diagOp blk (c * c') = diagOp blk c * diagOp blk c' ∧ diagOp blk (c + c') = diagOp blk c + diagOp blk c' ∧
    diagOp blk (fun _ => z) = z • 1 ∧ star (diagOp blk c) = diagOp blk (star c)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locOp {w : Pl E} (σ : SmIrr (UL n w)) (K' : Subgroup (UL n w)) (f : UL n w → ℂ) : Module.End ℂ (fixed σ.ρ K') :=
  if h : ∀ v ∈ fixed σ.ρ K', levOp σ.ρ (KL n w) K' f LinearMap.id v ∈ fixed σ.ρ K' then
    (levOp σ.ρ (KL n w) K' f LinearMap.id).restrict h else 0

def lconv {w : Pl E} (f₁ f₂ : UL n w → ℂ) (y : UL n w) : ℂ := hint (KL n w) fun z => f₁ z * f₂ (z⁻¹ * y)

def lstar {w : Pl E} (f : UL n w → ℂ) (y : UL n w) : ℂ := starRingEnd ℂ (f y⁻¹)

def LocAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w))
  (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ f₁ f₂ : UL n w → ℂ, IsHecke K' f₁ → IsHecke K' f₂ →
    twTr σ.ρ (KL n w) K' f₁ LinearMap.id = LinearMap.trace ℂ _ (locOp σ K' f₁) ∧
    (∀ v : fixed σ.ρ K', (locOp σ K' f₁ v).1 = levOp σ.ρ (KL n w) K' f₁ LinearMap.id v.1) ∧
    IsHecke K' (lconv f₁ f₂) ∧ IsHecke K' (lstar f₁) ∧ locOp σ K' (lconv f₁ f₂) = locOp σ K' f₁ * locOp σ K' f₂ ∧
    (∀ z : ℂ, locOp σ K' (f₁ + z • f₂) = locOp σ K' f₁ + z • locOp σ K' f₂) ∧
    IsHecke K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) ∧
    locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) = 1

def SphOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E)
  (σ : SmIrr (UL n w)), fixed σ.ρ (KL n w) ≠ ⊥ → FiniteDimensional ℂ (fixed σ.ρ (KL n w)) →
    Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1

def CompUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (w : Pl E) (σ : SmIrr (UL n w)), IsCompU π w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ

def SphStar : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w)),
  GlobalTheory.SmGL.IsUnitarisable σ.ρ → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 → ∀ h₁ h₂, IsHecke (KL n w) h₁ → IsHecke (KL n w) h₂ →
    twTr σ.ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr σ.ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id = starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) ∧
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1

def IsCong {w : Pl E} (m : ℕ) (K' : Subgroup (UL n w)) : Prop :=
  ∀ k, k ∈ K' ↔ k ∈ KL n w ∧ ∀ i j, Valued.v ((k.1.val - 1) i j) ≤ WithZero.exp (-(m : ℤ))

def LevelEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ (R : Finset (Pl E)) (M : ℕ),
    ∃ (K₀ : ∀ w : Pl E, Subgroup (UL n w)) (m : ℕ), M ≤ m ∧ 1 ≤ m ∧ IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₀ ∧
      (∀ w, IsUnramU π w → w ∉ R → K₀ w = KL n w) ∧ (∀ w, ¬ IsUnramU π w ∨ w ∈ R → IsCong m (K₀ w)) ∧
      ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ K₀ w) → HasLevel S π K'

def SplitDict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ σ : SmIrr (UL n w), ∃ (P : SmIrr (GLw n w)) (T : σ.V ≃ₗ[ℂ] P.V), (∀ (x : UL n w) y, T (σ.ρ x y) = P.ρ x.1 (T y)) ∧
    (∀ π : Submodule ℂ (UA E n → ℂ), IsCompU π w σ → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) ∧
    ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ e : GLw n w → ℂ,
      PositivityTheory.Rg.BcN.F2.IsHk (K'.map (UL n w).subtype) e → IsHecke K' (fun x => e x.1) ∧ ∀ y ∈ fixed σ.ρ K',
        T y ∈ fixed P.ρ (K'.map (UL n w).subtype) ∧
        T (levOp σ.ρ (KL n w) K' (fun x => ((K'.relIndex (KL n w) : ℕ) : ℂ) * e x.1) LinearMap.id y) =
          PositivityTheory.Rg.BcN.F2.hk P.ρ (K'.map (UL n w).subtype) e (T y)

def SpecTrace : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (B : Finset (Pl E)),
  (↑B : Set (Pl E)) ⊆ S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
  (∀ w ∈ S, w ∉ B → K' w = KL n w) → ∀ (ι : Type) [Fintype ι] (σ : ι → ∀ w : Pl E, SmIrr (UL n w)),
  (∀ i, ∀ w ∈ S, FiniteDimensional ℂ (fixed (σ i w).ρ (K' w))) →
  (∀ i, ∀ w ∈ S, w ∉ B → Module.finrank ℂ (fixed (σ i w).ρ (KL n w)) = 1) → ∀ g : ∀ w : Pl E, UL n w → ℂ,
    ∃ (d : ℕ) (blk : Fin d → ι) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)),
      (∀ c, Commute u (diagOp blk c)) ∧
      (∀ (k : ℕ) f, IsTest (KL n) K' f → (∀ i, ∀ w ∈ B, locOp (σ i w) (K' w) (f w) = locOp (σ i w) (K' w) (g w) ^ k) →
        ∑ i, ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
          LinearMap.trace ℂ _ ((u ^ k * diagOp blk fun i => ∏ᶠ w ∈ S \ ↑B, twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id :
            EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))) ∧
      ∀ i₀, (∀ w ∈ B, ∃ y, y ≠ 0 ∧ locOp (σ i₀ w) (K' w) (g w) y = y) → ∃ v, v ≠ 0 ∧ u v = v ∧ ∀ c, diagOp blk c v = c i₀ • v

end PositivityTheory.Rg.BcB.F.Eig

end
