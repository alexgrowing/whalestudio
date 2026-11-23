import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace CompanionTheory.PRW.ACWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

def algChar (w : HeightOneSpectrum (𝓞 E)) (m : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ)
    (x : w.adicCompletion E) : Qbar l :=
  ∏ᶠ j : {j : w.adicCompletion E →+* Qbar l // Continuous j}, j.1 x ^ (-m j)

def phiVB (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] : V ⊗[ℚ_[l]] P.R.B →ₗ[LL] V ⊗[ℚ_[l]] P.R.B :=
  AlgebraTensorModule.map LinearMap.id P.φB.toLinearMap

def ent {G : Type} [Group G] {LL : FinExt l} (ψ : G →* GL (Fin 1) ↥LL.1) (g : G) : Qbar l :=
  (((ψ g : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 : ↥LL.1)

def ConradLocalTiedness : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
      ∀ (LL : FinExt l) (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ g, ‖ent ψ g‖ = 1) →
      (Bw.IsCrysE P LL ψ ↔ ∃ m : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ,
        (∀ x : (w.adicCompletion E)ˣ, algChar w m (x : w.adicCompletion E) ∈ LL.1) ∧
        ∀ σ : Weil h, IsUnitAt w (a σ) → ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = algChar w m ((a σ)⁻¹ : (w.adicCompletion E)ˣ)) ∧
      ∀ m : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ,
        (∀ x : (w.adicCompletion E)ˣ, algChar w m (x : w.adicCompletion E) ∈ LL.1) →
        (∀ σ : Weil h, IsUnitAt w (a σ) → ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = algChar w m ((a σ)⁻¹ : (w.adicCompletion E)ˣ)) →
        ∀ (π : (w.adicCompletion E)ˣ) (σπ : Weil h), IsUnifAt w π → a σπ = π⁻¹ →
        ∀ x ∈ Dcris (P.PD Bw.Kw) (Bw.repE LL ψ),
          ∃ c : ↥LL.1, (c : Qbar l) = (ent ψ ⟨σπ, Weil_le_Dec h σπ.2⟩)⁻¹ * algChar w m (π : w.adicCompletion E) ∧
            (phiVB P (LL := ↥LL.1) ^ GlobalTheory.Pst.resDeg l w) x = c • x

end CompanionTheory.PRW.ACWD

end
