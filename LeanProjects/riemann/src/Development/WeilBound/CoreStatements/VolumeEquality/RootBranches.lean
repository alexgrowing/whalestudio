import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Filter Topology Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

def HolNull : Prop :=
  ∀ (X : Scheme.{0}) (n : ℕ) (B : Set (Fin n → ℂ)) (y : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens), IsOpen B → IsPreconnected B →
    IsHolTo B y → (∃ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ U) → volume {b ∈ B | ¬ ⊤ ≤ y b ⁻¹ᵁ U} = 0

def ChartMeets : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (U : X.Opens),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → IsArithVar (mCoordIdeal y) (n + 1) →
    genPt ξ ∈ U → ∃ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z (χ.γ t) ∧ ⊤ ≤ z ⁻¹ᵁ U

def monicOf {d : ℕ} (a : Fin d → ℂ) : ℂ[X] := X ^ d + ∑ i, C (a i) * X ^ (i : ℕ)

def RootBranches : Prop :=
  ∀ (n d : ℕ) (T : Set (Fin n → ℂ)) (a : (Fin n → ℂ) → Fin d → ℂ), IsOpen T → DifferentiableOn ℂ a T →
    (∀ t ∈ T, (monicOf (a t)).Separable) → ∀ t₀ ∈ T, ∃ (V : Set (Fin n → ℂ)) (θ : Fin d → (Fin n → ℂ) → ℂ),
      IsOpen V ∧ t₀ ∈ V ∧ V ⊆ T ∧ (∀ i, DifferentiableOn ℂ (θ i) V) ∧
        ∀ t ∈ V, (Function.Injective fun i => θ i t) ∧ ∀ x, (monicOf (a t)).IsRoot x ↔ ∃ i, x = θ i t

def CoverRoots : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), 𝔐.IsCover d →
    ∃ (U : Y.X.Opens) (a : Fin d → Γ(Y.X, U)) (cf : (Σ k, J k) → Fin d → Γ(Y.X, U)), genPt 𝔐.ξ₀ ∈ U ∧
      ∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → (monicOf fun i => valAt' p U (a i)).Separable ∧
        (∀ θ, (monicOf fun i => valAt' p U (a i)).IsRoot θ → ∃ z : Sp ℂ ⟶ 𝔐.X, z ≫ 𝔐.f = p ∧
          CoordsAt 𝔐.ξ y z fun s => ∑ i, valAt' p U (cf s i) * θ ^ (i : ℕ)) ∧
        (∀ z : Sp ℂ ⟶ 𝔐.X, z ≫ 𝔐.f = p → ∃ θ, (monicOf fun i => valAt' p U (a i)).IsRoot θ ∧
          CoordsAt 𝔐.ξ y z fun s => ∑ i, valAt' p U (cf s i) * θ ^ (i : ℕ)) ∧
        ∀ θ θ' (z : Sp ℂ ⟶ 𝔐.X), (monicOf fun i => valAt' p U (a i)).IsRoot θ → (monicOf fun i => valAt' p U (a i)).IsRoot θ' →
          (CoordsAt 𝔐.ξ y z fun s => ∑ i, valAt' p U (cf s i) * θ ^ (i : ℕ)) →
          (CoordsAt 𝔐.ξ y z fun s => ∑ i, valAt' p U (cf s i) * θ' ^ (i : ℕ)) → θ = θ'

def InLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Tor.Level H) (D : Datum H)
    (γ : D.La ≃ₗ[𝓞 E] D.La) : Prop :=
  (∀ a b, D.EF (γ a) (γ b) = D.EF a b) ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, γ a = a + l.M • e) ∧ ∀ a, ∃ e, γ a = a + l.A • e

def LocInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (D : Datum H) (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (F : UnivFam E Ψ j j' n g D.La) (Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La)), (F.form = D.EF ∨ F.form = -D.EF) →
    (∀ γ ∈ Γ, InLevel l D γ) → ∀ t₀ ∈ ballDom F.q, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ ballDom F.q ∧
      ∀ t ∈ V, ∀ t' ∈ V, F.Eqv Γ t t' → t = t'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

structure BaseUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ) where
  np : ℕ
  g : ℕ
  Di : Fin np → Datum H
  sig : ∀ k, (Di k).p = D.p ∧ (Di k).q = D.q
  κ : Fin np → (c.F →+* ℂ)
  F : ∀ k, UnivFam E (CMType H) j j' n g (Di k).La
  q_eq : ∀ k k', (F k).q = (F k').q
  form_eq : ∀ k, (F k).form = (Di k).EF ∨ (F k).form = -(Di k).EF
  σ_eq : ∀ k τ, (F k).σ τ = (κ k).comp (labelEmb c (sm τ))
  Γ : ∀ k, Subgroup ((Di k).La ≃ₗ[𝓞 E] (Di k).La)
  mem_Γ : ∀ k γ, γ ∈ Γ k ↔ InLevel l (Di k) γ
  arith : ∀ k, (F k).IsArith (Γ k)
  pt : Fin np → (Fin n → ℂ) → (Sp ℂ ⟶ Y.X)
  hol : ∀ k, IsHolTo (ballDom (F k).q) (pt k)
  comp_s_eq_spMap_of_isOver : ∀ k, ∀ t ∈ ballDom (F k).q, pt k t ≫ Y.s = spMap ((κ k).comp (algebraMap (𝓞 c.F) c.F))
  interior : ∀ k, ∀ t ∈ ballDom (F k).q, centre (pt k t) ∈ abLocus Y.t.G
  disj : ∀ k k', ∀ t ∈ ballDom (F k).q, ∀ t' ∈ ballDom (F k').q, pt k t = pt k' t' → k = k'
  fibre : ∀ k, ∀ t ∈ ballDom (F k).q, ∀ t' ∈ ballDom (F k).q, pt k t = pt k t' ↔ (F k).Eqv (Γ k) t t'
  onto : ∀ p : Sp ℂ ⟶ Y.X, centre p ∈ abLocus Y.t.G → ∃ k, ∃ t ∈ ballDom (F k).q, pt k t = p
  lat : ∀ k, ∀ t ∈ ballDom (F k).q, FibreLat Y.t (pt k t) ((F k).R t)

  vec : ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (k : Fin np) (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), IsOpen V → V ⊆ ballDom (F k).q →
    IsHolTo V z → (∀ t ∈ V, z t ≫ 𝔐.f = pt k t) → ∀ t₀ ∈ V, ∀ (m : ℕ) (s : Fin m → 𝔐.Li), (∀ a, ∃ v, 𝔐.M.ValAt (z t₀) (s a) v) →
      ∃ x : Fin m → (Fin n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ 𝔐.t.G),
        (∀ a, 𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec 𝔐.t (z t) ((F k).R t) (fun a => x a t) v

def BaseUnifEx : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ), 1 ≤ D.p + D.q →
    (sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p) → n = Fintype.card (CMType H) * j * j' →
    Nonempty (BaseUnif Y sm j j' n)

end SheetDecomposition
