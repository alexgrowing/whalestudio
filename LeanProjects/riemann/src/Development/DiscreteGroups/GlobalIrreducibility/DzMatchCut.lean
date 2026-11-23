import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def gs {g : ℕ} (ψ₀ : AddChar (ZMod g) Circle) {K : Type} [Field K] [Algebra (ZMod g) K] (η : Kˣ →* ℂˣ) : ℂ :=
  ∑ᶠ z : Kˣ, (η z : ℂ) * (ψ₀ (Algebra.trace (ZMod g) K (z : K)) : ℂ)

def nmChar {g : ℕ} (K : Type) [Field K] [Algebra (ZMod g) K] (χ : (ZMod g)ˣ →* ℂˣ) : Kˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm (ZMod g) : K →* ZMod g))

def IsGamma {g n : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g n)) (γ : ℂ) : Prop :=
  ∀ v : τ, ∑ᶠ y : Gn g n, (ψ₀ (Matrix.trace (y : Mt g n)) : ℂ) • τ.ρ y⁻¹ v = γ • v

def IsLower {g m : ℕ} (b : Gn g m) : Prop := ∀ i j : Fin m, i < j → (b : Mt g m) i j = 0

def IsCell {g m : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) (W : Gn g m → ℂ) : Prop :=
  (∀ u ∈ unipB (ZMod g) (Fin m), ∀ x, W (u * x) = ((ψ₀ (superDiag u))⁻¹ : Circle) * W x) ∧
    (∀ b, IsLower b → ∀ x, W (x * b) = W x) ∧ W 1 ≠ 0

def FinEq {g m : ℕ} [Fact g.Prime] (τ : FDRep ℂ (Gn g (m + 1))) (l : Module.Dual ℂ τ) (W : Gn g m → ℂ) (s : ℂ) : Prop :=
  ∀ v : τ, ∑ᶠ x : Gn g m, l (τ.ρ (tilde (corner x)) v) * W (tilde x) = s * ∑ᶠ x : Gn g m, l (τ.ρ (corner x) v) * W x

def Lifts1 {g : ℕ} [Fact g.Prime] {k : Type} [Field k] (i : ℚ_[g] ≃+* k) (ψ₀ : AddChar (ZMod g) Circle)
    (ψ : AddChar k Circle) : Prop := ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)

def LiftsChar {g : ℕ} [Fact g.Prime] {k : Type} [Field k] (i : ℚ_[g] ≃+* k) (χ₀ : (ZMod g)ˣ →* ℂˣ)
    (χ : kˣ →* ℂˣ) : Prop :=
  (∀ (u : ℤ_[g]ˣ) (x : kˣ), (x : k) = i ((u : ℤ_[g]) : ℚ_[g]) →
    χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u)) ∧ ∀ x : kˣ, (x : k) = (g : k) → χ x = 1

def HasCellVec {g m : ℕ} [Fact g.Prime] {k : Type} [Field k] (i : ℚ_[g] ≃+* k) (ψ : AddChar k Circle)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin m) k) V) : Prop :=
  ∃ (l : Module.Dual ℂ V) (v : V), IsFunctional ψ⁻¹ ρ l ∧ l v ≠ 0 ∧
    ∀ x : GL (Fin m) ℤ_[g], IsLower (GlobalTheory.GLp.red g m x) →
      ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g m x)) v = v

def NarrowBig : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → (n = 1 ∨ 16 * n ^ 2 < g) → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

def LMatchBig : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → (n = 1 ∨ 16 * n ^ 2 < g) → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) →
      ∃ k : ℕ, ∀ z : Kˣ, ξ z = θ (z ^ g ^ k)

def LOne : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → n = 1 → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) →
      ∃ k : ℕ, ∀ z : Kˣ, ξ z = θ (z ^ g ^ k)

def LPin : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 2 ≤ n → 16 * n ^ 2 < g →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Nat.card K = g ^ n →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 → ∀ θ ξ : Kˣ →* ℂˣ,
      GlobalTheory.Published.IsRegularChar g n θ → GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ χ₀ : (ZMod g)ˣ →* ℂˣ, ∃ r : ℕ, 0 < r ∧
        (gs ψ₀ (θ * nmChar K χ₀)⁻¹ * gs ψ₀ ξ⁻¹) ^ r = (gs ψ₀ (ξ * nmChar K χ₀)⁻¹ * gs ψ₀ θ⁻¹) ^ r) →
      ∃ k : ℕ, ∀ z : Kˣ, ξ z = θ (z ^ g ^ k)

def LKondo : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 2 ≤ n → 16 * n ^ 2 < g →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Nat.card K = g ^ n →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 → ∃ κ : ℂ, κ ≠ 0 ∧
      ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ → ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
      IsGamma ψ₀ τ (κ * gs ψ₀ θ⁻¹)

def LFE : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (m : ℕ) (ψ₀ : AddChar (ZMod g) Circle), ψ₀ ≠ 1 →
    ∀ τ : FDRep ℂ (Gn g (m + 1)), IsCusp τ.character → ∀ γ : ℂ, IsGamma ψ₀ τ γ →
    ∀ l : Module.Dual ℂ τ, IsFunctional ψ₀ τ.ρ l →
    ∀ x : τ, (∀ b : Gn g m, IsLower b → τ.ρ (corner b) x = x) →
      (g : ℂ) ^ (m * (m + 1) ^ 2 / 2) * l (τ.ρ (longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g))) x) =
        γ ^ m * l x

def FinPair : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (m : ℕ) (ψ₀ : AddChar (ZMod g) Circle), ψ₀ ≠ 1 →
    ∀ τ : FDRep ℂ (Gn g (m + 1)), IsCusp τ.character → ∀ γ : ℂ, IsGamma ψ₀ τ γ →
    ∀ l : Module.Dual ℂ τ, IsFunctional ψ₀ τ.ρ l → l ≠ 0 → ∀ W : Gn g m → ℂ, IsCell ψ₀ W →
    ∀ s : ℂ, FinEq τ l W s → (g : ℂ) ^ (m * (m + 1) ^ 2 / 2) * s = γ ^ m

def LFinPair : Prop := LFE → FinPair

def LPsi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 →
      ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ Lifts1 i ψ₀ ψ

def GenSph : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 → ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → Lifts1 i ψ₀ ψ →
    ∀ m : ℕ, ∃ (τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ),
      IsSpherical (cls τ₀).rep ∧ HasCentralChar τ₀.ρ ω ∧ HasCellVec i ψ τ₀.ρ

def LGen : Prop := GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GenSph

def Red : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 → ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → Lifts1 i ψ₀ ψ →
    ∀ (m : ℕ) (τ : FDRep ℂ (Gn g (m + 1))), IsCusp τ.character →
    ∀ σ : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E)), IsCuspidal σ.ρ →
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ (τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ),
      HasCentralChar τ₀.ρ ω → HasCellVec i ψ τ₀.ρ → ∀ e : ℂ, HasPairEps ψ σ.ρ τ₀.ρ e →
      ∃ (l : Module.Dual ℂ τ) (W : Gn g m → ℂ), IsFunctional ψ₀ τ.ρ l ∧ l ≠ 0 ∧ IsCell ψ₀ W ∧
        FinEq τ l W ((ω (-1) : ℂ) ^ m * e)

def LRed : Prop := DiscreteGroups.sglob.LConv.CuspGen → Red

def LTw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ (n : ℕ) (K : Type) [Field K] [Algebra (ZMod g) K], Nat.card K = g ^ n → 0 < n →
    ∀ χ₀ : (ZMod g)ˣ →* ℂˣ, ∃ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ), LiftsChar i χ₀ χ ∧
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ → ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      ∃ (τ' : FDRep ℂ (Gn g n)) (σ' : IrrRep (GL (Fin n) (w.adicCompletion E))),
        GlobalTheory.Published.IsRegularChar g n (θ * nmChar K χ₀) ∧ IsCusp τ'.character ∧
        (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ'.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (((θ * nmChar K χ₀) (z ^ g ^ j) : ℂˣ) : ℂ)) ∧
        GlobalTheory.SerSys.TameGen.Inflates (σ'.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ' ∧
        cls σ' = (cls σ).tw χ hχ

def TameRec : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A v),
    ((g : ℕ) : 𝓞 M) ∈ v.asIdeal → ((g : ℕ) : 𝓞 M) ∉ v.asIdeal ^ 2 →
    ∀ a : Weil h →* (v.adicCompletion M)ˣ, IsLocalArtin h a →
    ∀ π : Ω, π ^ (normV v - 1) = (g : Ω) → ∀ (t : Ine (F := M) A) (x : 𝓞 M),
      Valued.v ((a (ineIncl h t) : v.adicCompletion M) - algebraMap M (v.adicCompletion M) (x : M)) < 1 →
      A.valuation ((t : G M Ω) π / π - algebraMap M Ω (x : M)) < 1

def LTameRec : Prop := GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.ChevalleyUnits → TameRec

def GalEps : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 2 ≤ n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A), IsDeligneEps ε →
    ∀ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 → ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ y : WD h, IsIrrWD y → IsTameWD y → y.lpDim = n →
    ∀ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        y.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) →
    ∀ u : WD h, u.unr →
    ∀ (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ), LiftsChar i χ₀ χ →
      ∃ r : ℕ, 0 < r ∧
        ((ε E w h ψ ((y.lpTwist (χ.comp a) (ha.smooth hχ)).lpChar u) : ℂ) * gs ψ₀ ξ⁻¹ ^ u.lpDim) ^ r =
          ((ε E w h ψ (y.lpChar u) : ℂ) * gs ψ₀ (ξ * nmChar K χ₀)⁻¹ ^ u.lpDim) ^ r

def LGal : Prop := GlobalTheory.Published.LocalLanglandsGL → TameRec → GalEps

def LOneOf : Prop := TameRec → LOne

theorem aut_eps (HFP : FinPair) (HR : Red) {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ}
    [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (ψ₀ : AddChar (ZMod g) Circle) (h₀ : ψ₀ ≠ 1)
    (ψ : AddChar (w.adicCompletion E) Circle) (hc : Continuous ψ) (hl : Lifts1 i ψ₀ ψ) (m : ℕ)
    (τ : FDRep ℂ (Gn g (m + 1))) (hτ : IsCusp τ.character) (γ : ℂ) (hγ : IsGamma ψ₀ τ γ)
    (σ : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (hσ : IsCuspidal σ.ρ)
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ)
    (τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar τ₀.ρ ω)
    (hv : HasCellVec i ψ τ₀.ρ) (e : ℂ) (he : HasPairEps ψ σ.ρ τ₀.ρ e) :
    (g : ℂ) ^ (m * (m + 1) ^ 2 / 2) * ((ω (-1) : ℂ) ^ m * e) = γ ^ m := by
  obtain ⟨l, W, h1, h2, h3, h4⟩ := HR E w g i hi ψ₀ h₀ ψ hc hl m τ hτ σ hσ hs τ₀ ω hω hv e he
  exact HFP g m ψ₀ h₀ τ hτ γ hγ l h1 h2 W h3 _ h4

theorem exists_addChar (g : ℕ) [Fact g.Prime] : ∃ ψ₀ : AddChar (ZMod g) Circle, ψ₀ ≠ 1 := by
  refine ⟨ZMod.toCircle, fun h => ?_⟩
  have h1 : (ZMod.toCircle (1 : ZMod g)) = ZMod.toCircle (0 : ZMod g) := by rw [h]; rfl
  exact one_ne_zero (ZMod.injective_toCircle h1)

theorem lMatchBig_of (H1 : LCusp) (H2 : LDepth) (HO : LOne) (HP : LPin) (HK : LKondo) (HFP : FinPair) (HPs : LPsi)
    (HG : GenSph) (HR : Red) (HT : LTw) (HE : GalEps) : LMatchBig := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hbig hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs
    ξ hξ hξf
  by_cases h1 : n = 1
  · exact HO E E' Ω g A w h w' h' rc hrc i hi n hn h1 hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs ξ hξ hξf
  have hb : 16 * n ^ 2 < g := hbig.resolve_left h1
  have h2 : 2 ≤ n := by omega
  have hcard : Nat.card K = g ^ n := by
    have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
      (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
    rw [← hN, normV, Nat.card_congr e.toEquiv]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  obtain ⟨ψ₀, h₀⟩ := exists_addChar g
  obtain ⟨ψ, hc, hψ, hl⟩ := HPs E w g i hi ψ₀ h₀
  obtain ⟨τ₀, ω, hsph, hω, hv⟩ := HG E w g i hi ψ₀ h₀ ψ hc hl m
  obtain ⟨κ, hκ, hKo⟩ := HK g (m + 1) h2 hb K hcard ψ₀ h₀
  have hcu : ∀ (τ' : FDRep ℂ (Gn g (m + 1))), IsCusp τ'.character →
      ∀ σ' : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ'.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ' → IsCuspidal σ'.ρ :=
    fun τ' hτ' σ' hs' => (IrrGL.isCusp_of.1 (H1 E w g i hi (m + 1) hn τ' hτ' σ' hs')).2
  have hy : IsIrrWD (rc (cls σ)) := (hL.cusp _).1 (H1 E w g i hi _ hn τ hτ σ hs)
  have ht : IsTameWD (rc (cls σ)) := (hL.depth _).1 (H2 E w g i hi _ τ σ hs)
  have hu : (rc (cls τ₀)).unr := (hL.sph _).1 hsph
  have hdu : (rc (cls τ₀)).lpDim = m := hL.dim _
  have e1 := aut_eps HFP HR i hi ψ₀ h₀ ψ hc hl m τ hτ _ (hKo θ hθ τ hτ hf) σ (hcu τ hτ σ hs) hs τ₀ ω hω hv _
    (hL.eps ψ hc hψ m σ τ₀ (hcu τ hτ σ hs))
  refine HP g (m + 1) h2 hb K hcard ψ₀ h₀ θ ξ hθ hξ fun χ₀ => ?_
  obtain ⟨χ, hχ, hlc, htw⟩ := HT E w g i hi (m + 1) K hcard hn χ₀
  obtain ⟨τ', σ', hθ', hτ', hf', hs', hcl⟩ := htw θ hθ τ hτ hf σ hs
  have e2 := aut_eps HFP HR i hi ψ₀ h₀ ψ hc hl m τ' hτ' _ (hKo _ hθ' τ' hτ' hf') σ' (hcu τ' hτ' σ' hs') hs' τ₀ ω hω hv _
    (hL.eps ψ hc hψ m σ' τ₀ (hcu τ' hτ' σ' hs'))
  rw [hcl, hL.tw_eq] at e2
  obtain ⟨r, hr0, e3⟩ := HE E E' Ω g A w h w' h' i hi (m + 1) h2 hg hN a' ha' K red hr hk a ha ε hε ψ₀ h₀ ψ hc hψ
    (rc (cls σ)) hy ht (hL.dim _) ξ hξ hξf (rc (cls τ₀)) hu χ₀ χ hχ hlc
  rw [hdu] at e3
  refine ⟨m * r, Nat.mul_pos (by omega) hr0, ?_⟩
  have hκr : (κ ^ m) ^ r ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hκ)
  refine mul_left_cancel₀ hκr ?_
  generalize (ε E w h ψ (((rc (cls σ)).lpTwist (χ.comp a) (ha.smooth hχ)).lpChar (rc (cls τ₀))) : ℂ) = e' at e2 e3
  generalize (ε E w h ψ ((rc (cls σ)).lpChar (rc (cls τ₀))) : ℂ) = e at e1 e3
  generalize (g : ℂ) ^ (m * (m + 1) ^ 2 / 2) = Q at e1 e2
  generalize (ω (-1) : ℂ) ^ m = o at e1 e2
  have f1 : κ ^ m * (gs ψ₀ (θ * nmChar K χ₀)⁻¹ * gs ψ₀ ξ⁻¹) ^ m = Q * o * (e' * gs ψ₀ ξ⁻¹ ^ m) := by
    rw [mul_pow, ← mul_assoc, ← mul_pow, ← e2]; ring
  have f2 : κ ^ m * (gs ψ₀ (ξ * nmChar K χ₀)⁻¹ * gs ψ₀ θ⁻¹) ^ m =
      Q * o * (e * gs ψ₀ (ξ * nmChar K χ₀)⁻¹ ^ m) := by
    rw [mul_pow, mul_left_comm, ← mul_pow, ← e1]; ring
  rw [pow_mul, pow_mul, ← mul_pow (κ ^ m), ← mul_pow (κ ^ m), f1, f2, mul_pow (Q * o), mul_pow (Q * o), e3]

theorem narrowBig_of (H1 : LCusp) (H2 : LDepth) (H3 : LTame) (H4 : LMatchBig) : NarrowBig := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hbig hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs
    t x z hxz hv
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have hrc' : IsRec h rc := ⟨a, ha, ε, hε, hL⟩
  have hc : IsIrrWD (rc (cls σ)) := (hL.cusp _).1 (H1 E w g i hi n hn τ hτ σ hs)
  have ht : IsTameWD (rc (cls σ)) := (hL.depth _).1 (H2 E w g i hi n τ σ hs)
  have hd : (rc (cls σ)).lpDim = n := hL.dim _
  obtain ⟨ξ, hξ, hξf⟩ := H3 E E' Ω g A w h w' h' i hi n hn hg hN a' ha' K red hr hk (rc (cls σ)) hc ht hd
  obtain ⟨k, hk'⟩ := H4 E E' Ω g A w h w' h' rc hrc' i hi n hn hbig hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs ξ hξ hξf
  rw [hξf t x z hxz hv]
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hz := pow_card_units w' g n hN K red hr hk hpos z
  have e1 : ∀ j, ((ξ (z ^ g ^ j) : ℂˣ) : ℂ) = ((θ (z ^ g ^ (j + k)) : ℂˣ) : ℂ) := fun j => by
    rw [hk', ← pow_mul, ← pow_add]
  simp_rw [e1]
  refine prod_shift (fun j => ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) n (fun j => ?_) k
  show ((θ (z ^ g ^ (j + n)) : ℂˣ) : ℂ) = ((θ (z ^ g ^ j) : ℂˣ) : ℂ)
  rw [pow_add, mul_comm, pow_mul, hz]

theorem narrowBig_of_leaves (H1 : LCusp) (H2 : LDepth) (H3 : LTame) (hO : LOneOf) (hP : LPin) (hK : LKondo) (hFE : LFE)
    (hFP : LFinPair) (hPs : LPsi) (hG : LGen) (hR : LRed) (hT : LTw) (hTR : LTameRec) (hE : LGal)
    (cg : DiscreteGroups.sglob.LConv.CuspGen) (art : GlobalTheory.Published.GlobalArtinReciprocity) (chev : GlobalTheory.Published.ChevalleyUnits)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : NarrowBig :=
  narrowBig_of H1 H2 H3 (lMatchBig_of H1 H2 (hO (hTR art chev)) hP hK (hFP hFE) hPs (hG bern) (hR cg) hT
    (hE hL (hTR art chev)))

end DiscreteGroups.sglob.DzType
