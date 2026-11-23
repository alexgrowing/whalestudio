import Mathlib
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.ConradLocalTiedness

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PY

def ConradLocalTied : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
      ∀ (LL : FinExt l) (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ g, ‖ent ψ g‖ = 1) →
      ∀ m : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ,
        (∀ x : (w.adicCompletion E)ˣ, algChar w m (x : w.adicCompletion E) ∈ LL.1) →
        (∀ σ : Weil h, IsUnitAt w (a σ) → ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = algChar w m ((a σ)⁻¹ : (w.adicCompletion E)ˣ)) →
        Bw.IsCrysE P LL ψ ∧
        (∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
          (∀ x : E, j.1 (algebraMap E (w.adicCompletion E) x) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) →
          ∀ n : ℤ, Bw.multE P LL ψ τ' n = if n = -m j then 1 else 0) ∧
        ∀ (π : (w.adicCompletion E)ˣ) (σπ : Weil h), IsUnifAt w π → a σπ = π⁻¹ →
        ∀ x ∈ Dcris (P.PD Bw.Kw) (Bw.repE LL ψ),
          ∃ c : ↥LL.1, (c : Qbar l) = (ent ψ ⟨σπ, Weil_le_Dec h σπ.2⟩)⁻¹ * algChar w m (π : w.adicCompletion E) ∧
            (phiVB P (LL := ↥LL.1) ^ GlobalTheory.Pst.resDeg l w) x = c • x

end GlobalTheory.PY

end
