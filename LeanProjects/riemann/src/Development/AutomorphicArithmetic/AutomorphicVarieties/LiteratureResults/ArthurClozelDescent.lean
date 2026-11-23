import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.V.Lit

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

def IsUnitaryR (π : TR.CuspSub E a) : Prop :=
  ∃ ω : HChar E, ω.IsUnitary ∧ ∀ φ ∈ π.V, ∀ (z : Ideles E) (g : GA E a),
    φ.1 (Matrix.GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g

omit [IsTotallyReal E] in

def IsAdExt (σ : E →+* E) (s : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E) E) : Prop :=
  Continuous s ∧ ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (σ x)

def IsPull (s : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E) E) (π π' : TR.CuspSub E a) : Prop :=
  ∀ φ : TR.Sm E a, φ ∈ π'.V ↔ ∃ ψ ∈ π.V, ∀ g : GA E a, φ.1 g = ψ.1 (Matrix.GeneralLinearGroup.map s g)

def Isotyp (π : TR.CuspSub E a) (w : InfinitePlace E) {W : Type} [AddCommGroup W] [Module ℂ W] (A : Fin a → Fin a → Module.End ℂ W) : Prop :=
  ⨆ f : {f : π.V →ₗ[ℂ] W // ∀ (i j : Fin a) (φ ψ : π.V), ψ.1 = TR.Eop w i j φ.1 → f ψ = A i j (f φ)}, LinearMap.range f.1 = ⊤

def blk (a : ℕ) : Fin a ⊕ Fin a ≃ Fin (2 * a) := finSumFinEquiv.trans (finCongr (two_mul a).symm)

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def IsIndAt (P : TR.CuspSub F (2 * a)) (v : InfinitePlace F) (π π' : TR.CuspSub E a) (w : InfinitePlace E) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (A B : Fin a → Fin a → Module.End ℂ W) (L : P.V →ₗ[ℂ] W), L ≠ 0 ∧
    (∀ i j k l, A i j * B k l = B k l * A i j) ∧ Isotyp π w A ∧ Isotyp π' w B ∧ ∀ (i j : Fin a) (φ ψ : P.V),
      (ψ.1 = TR.Eop v (blk a (.inl i)) (blk a (.inr j)) φ.1 → L ψ = 0) ∧
      (ψ.1 = TR.Eop v (blk a (.inl i)) (blk a (.inl j)) φ.1 → L ψ = A i j (L φ) + (if i = j then (a : ℂ) / 2 else 0) • L φ) ∧
      (ψ.1 = TR.Eop v (blk a (.inr i)) (blk a (.inr j)) φ.1 → L ψ = B i j (L φ) - (if i = j then (a : ℂ) / 2 else 0) • L φ)

variable [Algebra F E]

def LiftsTo (P : TR.CuspSub F (2 * a)) (π π' : TR.CuspSub E a) : Prop :=
  WeakBC P.HasSat fun w B => ∃ B₁ B₂, π.HasSat w B₁ ∧ π'.HasSat w B₂ ∧ B = B₁ + B₂

end Defs

def ArthurClozelDescent : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E],
    Module.finrank F E = 2 → ∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ∀ s, IsAdExt (σ : E →+* E) s → ∀ a : ℕ, 1 ≤ a → ∀ π : TR.CuspSub E a, IsUnitaryR π →
      ∃ π' : TR.CuspSub E a, IsPull s π π' ∧ (π.Iso π' ∨ ∃ P : TR.CuspSub F (2 * a), IsUnitaryR P ∧ LiftsTo P π π' ∧
        ∀ η : HChar F, IsNormChar E η → P.Iso (P.twist η))

def Henniart4 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E],
    Module.finrank F E = 2 → ∀ a : ℕ, 1 ≤ a → ∀ (P : TR.CuspSub F (2 * a)) (π π' : TR.CuspSub E a), IsUnitaryR P → IsUnitaryR π →
      IsUnitaryR π' → LiftsTo P π π' → ∀ w : InfinitePlace E, IsIndAt P (w.comap (algebraMap F E)) π π' w

def AdExtEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (σ : E ≃+* E), ∃ s, IsAdExt (σ : E →+* E) s

def PullPar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (σ : E ≃+* E) s, IsAdExt (σ : E →+* E) s → ∀ (a : ℕ) (π π' : TR.CuspSub E a),
    IsPull s π π' → (IsUnitaryR π → IsUnitaryR π') ∧
      (∀ (w : InfinitePlace E) m, π.HasInfChar w m → π'.HasInfChar (w.comap (σ : E →+* E)) m) ∧
      ∀ (w w' : HeightOneSpectrum (𝓞 E)), (∀ x y : 𝓞 E, (y : E) = σ x → (x ∈ w'.asIdeal ↔ y ∈ w.asIdeal)) →
        ∀ B, π.HasSat w B → π'.HasSat w' B

def IndInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (P : TR.CuspSub F (2 * a))
    (v : InfinitePlace F) (π π' : TR.CuspSub E a) (w : InfinitePlace E), IsIndAt P v π π' w → ∀ m m' M, π.HasInfChar w m →
    π'.HasInfChar w m' → P.HasInfChar v M → M = m + m'

def InfEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a) (v : InfinitePlace F), ∃ m, π.HasInfChar v m

def UnitTw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] (a : ℕ), 1 ≤ a →
    ∀ π : TR.CuspSub E a, ∃ (s : ℝ) (χ : HChar E) (χ₀ : HChar F), IsUnitaryR (π.twist χ) ∧ (∀ v, TR.expo χ v = s) ∧ (∀ v, TR.expo χ₀ v = s) ∧
      (∀ w, χ.UnrAt w ∧ ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ)) ∧
      ∀ w, χ₀.UnrAt w ∧ ((χ₀.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ)

end UpperTheory.V.Lit
