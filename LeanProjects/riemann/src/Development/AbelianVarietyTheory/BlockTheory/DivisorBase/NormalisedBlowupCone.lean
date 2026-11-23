import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Pol

def PosForm (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Type :=
  {β : levelForms H 1 X // ∀ y, 0 ≤ (β : LinearMap.BilinForm ℤ X) y y}

variable {H : Host E}

abbrev PosForm.form {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (β : PosForm H X) : LinearMap.BilinForm ℤ X := β.1.1

def PosForm.ofLevel {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {N : ℕ} (γ : levelForms H N X)
    (h : ∀ y, 0 ≤ (γ : LinearMap.BilinForm ℤ X) y y) : PosForm H X :=
  ⟨⟨γ.1, γ.2.1, γ.2.2.1, fun _ _ => by simp⟩, h⟩

def IsCuspLattice (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Prop :=
  Module.Finite (𝓞 E) X ∧ Module.Projective (𝓞 E) X ∧ Module.finrank (𝓞 E) X ≤ q

def IsSemilinearOverK (H : Host E) {X X₁ : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁]
    (r : X →+ X₁) : Prop :=
  ∃ σ : 𝓞 E ≃+* 𝓞 E, σ H.rt = H.rt ∧ ∀ (a : 𝓞 E) (x : X), r (a • x) = σ a • r x

abbrev ConeFn (H : Host E) : Type 1 := ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], PosForm H X → ℕ

def IsPolarisation (q : ℕ) (ψ : ConeFn H) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], IsCuspLattice E q X → ∀ β : PosForm H X,
    (β.1 ≠ 0 → 0 < ψ X β) ∧
    ∃ ℓ : levelForms H 1 X →ₗ[ℤ] ℤ, ℓ β.1 = ψ X β ∧ ∀ γ : PosForm H X, (ψ X γ : ℤ) ≤ ℓ γ.1) ∧
  ∀ (X X₁ : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁],
    IsCuspLattice E q X → IsCuspLattice E q X₁ → ∀ r : X →+ X₁, Function.Surjective r → IsSemilinearOverK H r →
      ∀ (β : PosForm H X) (β₁ : PosForm H X₁), (∀ y z, β.form y z = β₁.form (r y) (r z)) → ψ X β = ψ X₁ β₁

theorem IsPolarisation.zero {q : ℕ} {ψ : ConeFn H} (h : IsPolarisation q ψ) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (hX : IsCuspLattice E q X) {β : PosForm H X} (e : β.1 = 0) : ψ X β = 0 := by
  obtain ⟨-, ℓ, h1, -⟩ := h.1 X hX β
  rw [e, map_zero] at h1
  omega

def IsConeOf (ψ : ConeFn H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {m : ℕ} (γ : Fin m → PosForm H X) : Prop :=
  ∃ (N : ℕ) (ℓ : levelForms H 1 X →ₗ[ℤ] ℤ), 0 < N ∧ ∀ β : PosForm H X,
    (N * ψ X β : ℤ) ≤ ℓ β.1 ∧
      ((N * ψ X β : ℤ) = ℓ β.1 ↔ ∃ (k : ℕ) (n : Fin m → ℕ), 0 < k ∧ k • β.1 = ∑ i, n i • (γ i).1)

def NoEquivalentRays {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {m : ℕ} (γ : Fin m → PosForm H X) : Prop :=
  ∀ (i j : Fin m) (g : X ≃+ X), IsSemilinearOverK H g.toAddMonoidHom →
    (∀ y z, (γ i).form y z = (γ j).form (g y) (g z)) → i = j

end Pol

section Blow

def IsNormalisedBlowup {U Z X : Scheme.{0}} (j : U ⟶ Z) (b : Z ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∃ (B : Scheme.{0}) (π : B ⟶ X) (j' : U ⟶ B) (_ : QuasiCompact j') (_ : QuasiSeparated j')
    (e : Z ≅ j'.normalization),
    FinalTheorems.Blowup π J ∧ j ≫ e.hom = j'.toNormalization ∧ e.hom ≫ j'.fromNormalization ≫ π = b

def IsRelAmpleIdeal {Z X : Scheme.{0}} (ρ : Z ⟶ X) (I : Z.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : Z), x ∈ ρ ⁻¹ᵁ U.1 →
    ∃ (n : ℕ) (s : Γ(Z, ρ ⁻¹ᵁ U.1)) (V : Z.affineOpens), 0 < n ∧ x ∈ V.1 ∧ V.1 ≤ ρ ⁻¹ᵁ U.1 ∧
      ∀ (y : Z) (hy : y ∈ ρ ⁻¹ᵁ U.1), Z.presheaf.germ _ y hy s ∈ FinalTheorems.stalkId I y ^ n ∧
        (y ∈ V.1 ↔ FinalTheorems.stalkId I y ^ n = Ideal.span {Z.presheaf.germ _ y hy s})

def idealAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] (χ : Sp R ⟶ X) : Ideal R :=
  ((J.comap χ).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

example {X : Scheme.{0}} {R : Type} [CommRing R] (χ : Sp R ⟶ X) : idealAlong ⊤ χ = ⊤ := by
  simp [idealAlong, Ideal.map_top]

end Blow

section Main

variable {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F}

def arcForm {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) : PosForm H a.D₀.X :=
  ⟨⟨a.be, a.be_symm, a.be_adj, fun _ _ => by simp⟩, fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (a.be_pos y h).le⟩

def chartRays {Z : Model Xo c β} {k : Type} [Field k] {m d : ℕ} {ξ : Sp (ChartRing k m d) ⟶ gen Z}
    {t : SAB H (Sp (ChartRing k m d))} {P : PELUnif (maximalIdeal (ChartRing k m d)) t}
    {γ : Fin m → levelForms H l.M' P.D.toPre.X} (h : IsToricChart Z ξ P γ) (i : Fin m) : PosForm H P.D.toPre.X :=
  PosForm.ofLevel (γ i) (h.forms.1 i)

def IsFanDivisor (Z : Model Xo c β) (ψ : ConeFn H) (I : (gen Z).IdealSheafData) : Prop :=
  FinalTheorems.EffCartier I ∧ (∀ x ∈ I.support, x ∈ genBd Z) ∧
  ∀ x ∈ genBd Z, ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z)
    (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H l.M' P.D.toPre.X) (h : IsToricChart Z ξ P γ),
    ξ (closedPoint _) = x ∧ IsCuspLattice E D.q P.D.toPre.X ∧ IsConeOf ψ (chartRays h) ∧
    NoEquivalentRays (chartRays h) ∧ idealAlong I ξ = Ideal.span {∏ i, bdParam k m d i ^ ψ _ (chartRays h i)}

def AbelianAtVertical [IsLocalRing O] (Z : Model Xo c β) : Prop :=
  ∀ η : Z.X, Z.s η = closedPoint O → (∀ x : Z.X, Z.s x = closedPoint O → x ⤳ η → x = η) → η ∈ abLocus Z.t.G

variable {Y : Model Xo c β}

def idealQ (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : (gen Y).IdealSheafData := I.map T.bQ

def idealInt (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Y.X.IdealSheafData := (idealQ T I).map (genι Y)

def ToricFacts (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Prop :=
  (idealQ T I).comap T.bQ = I ∧ IsRelAmpleIdeal T.bQ I ∧ IsNormalisedBlowup T.Z.jQ T.bQ (idealQ T I)

def IntegralBlowup (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Prop :=
  IsNormalisedBlowup T.Z.j T.b (idealInt T I) ∧ (idealInt T I).comap (genι Y) = idealQ T I ∧
    FinalTheorems.EffCartier ((idealInt T I).comap T.b) ∧ ((idealInt T I).comap T.b).comap (genι T.Z) = I

def ChartsMonomial (T : TorModel Y) (ψ : ConeFn H) (I : (gen T.Z).IdealSheafData) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : O →+* O') (ϖ : O') (a : ArcIn D l β O' b')
    (χ : Sp (PowerSeries O') ⟶ Y.X), IsArcBase O' ϖ → IsArcChart Y a ϖ χ →
      IsCuspLattice E D.q a.D₀.X ∧
      idealAlong (idealInt T I) χ = Ideal.span {PowerSeries.X ^ ψ _ (arcForm a)} ∧
      ∃ χ'' : Sp (PowerSeries O') ⟶ T.Z.X, χ'' ≫ T.b = χ ∧ IsArcChart T.Z a ϖ χ'' ∧
        ∀ χ₁ : Sp (PowerSeries O') ⟶ T.Z.X, χ₁ ≫ T.b = χ → χ₁ = χ''

def HasToroidalBlowup [IsLocalRing O] (Y : Model Xo c β) : Prop :=
  ∃ (ψ : ConeFn H) (T : TorModel Y) (I : (gen T.Z).IdealSheafData),
    IsPolarisation D.q ψ ∧ IsFanDivisor T.Z ψ I ∧ ToricFacts T I ∧ IntegralBlowup T I ∧ ChartsMonomial T ψ I ∧
    T.Z.LevelActs ∧ T.Z.N4 ∧ AbelianAtVertical T.Z

end Main

def ToroidalModelExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    IsAbelianGalois ℚ E → Odd (D.p + D.q) → D.q < D.p →
    ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), l.GoodAt p →
    ∀ Y : Model Xo c (c.V W).subtype, Y.LevelStructureConditions p → Y.SplitFibres → Y.N3 → Y.N4 → HasToroidalBlowup Y

end GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone
