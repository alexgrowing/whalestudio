import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

def Tied {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {F : Type} [Field F]
    (z : Spec (CommRingCat.of F) ⟶ 𝔐.X) (y₀ : Sp F ⟶ Xo.XF c) (vb : epsAt z ⟶ 𝔐.t.G)
    (v : epsAt (under y₀) ⟶ Xo.univ.t.G) : Prop :=
  ∃ v' : epsAt (y₀ ≫ Y.j) ⟶ Y.t.G, SameVec Y y₀ v v' ∧ vb.left ≫ 𝔐.m.φ = v'.left

def cP (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def CptEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y),
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), IsClopen U ∧ IsIrreducible U ∧ genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)

def PeriodOf : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U), 1 ≤ D.p → 1 ≤ D.q → IsClopen U → IsIrreducible U → Z.IsGeom →
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
        (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)

def SmoothLine : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (L : Lat ξ Ω)
    (a : K → ℤ) (e₀ c₀ : Ω) (cinf : (F' →+* ℂ) → ℝ) (n : ℕ),
    (∀ q : X, genPt ξ ⤳ q) → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ →
    OverInt y ψ → Birational y → IsArithVar (mCoordIdeal y) n → L.IsDegOn Set.univ y a e₀ →
    (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀)) → (∀ σ, 0 < cinf σ) →
    (∀ σ, cinf (ComplexEmbedding.conjugate σ) = cinf σ) →
    ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
      (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh →
        (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ (g h : MRing J) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
        (∀ k, (dg k : ℤ) - dh k = a k) ∧ aeval y g = c₀ * aeval y h ∧ evC w h ≠ 0

def PointEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p]),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ∃ (V L : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field L) (_ : CharZero L)
      (_ : Algebra V L) (_ : IsFractionRing V L) (j : L →+* ℂ_[p]) (ψL : F' →+* L) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X),
      (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) ∧ j.comp ψL = κ' ∧
      𝔐.Interior (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ∧
      (∀ a : F', ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (ψ a) (ψL a)) ∧
      ∀ a : F', ‖κ' a‖ ≤ 1 → ψ a ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩

def ValuePhi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (φ : FrameFn Xo c) (L : Type) [Field L] [CharZero L] (s : c.F →+* L)
    (z : Spec (CommRingCat.of L) ⟶ 𝔐.X) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li)
    (vp : Fin D.p → (epsAt z ⟶ 𝔐.t.G)) (vq : Fin D.q → (epsAt z ⟶ 𝔐.t.G)) (α κ : Ω) (u : L),
    CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → 𝔐.Interior z →
    (∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (s x)) → (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, 𝔐.all _⟩ →
    (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, 𝔐.all _⟩ → (∀ k, 𝔐.M.ValAt z (bp k) (vp k)) →
    (∀ k, 𝔐.M.ValAt z (bq k) (vq k)) → a' = α • exteriorPower.ιMulti Ω _ bp → b' = κ • exteriorPower.ιMulti Ω _ bq →
    ValAt 𝔐.ξ z (α / κ) u →
    ∃ (y₀ : Sp L ⟶ Xo.XF c) (v : Vecs y₀ D.p) (w : Vecs y₀ D.q), z ≫ 𝔐.f = y₀ ≫ Y.j ∧ IsFramed U τ.1 s y₀ v w ∧
      φ L y₀ v w = u ∧ (∀ k, Tied 𝔐 z y₀ (vp k) (v k)) ∧ ∀ k, Tied 𝔐 z y₀ (vq k) (w k)

def IntFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (y₀ : Sp L ⟶ Xo.XF c),
    (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ≫ 𝔐.f = y₀ ≫ Y.j →
    ∃ (T : SAB H (Sp V)) (tK : SAB H (Sp L)) (m : SABMap tK Xo.univ.t (under y₀))
      (m' : SABMap tK T (spMap (algebraMap V L))) (g : ℕ)
      (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (MU : LieModel Xo.univ.t.G (under y₀) (Fin g → L)) (ρC : 𝓞 E →+* Module.End L (Fin g → L)),
      MC.IsActOf 𝔐.t.act.act ρC ∧ MU.IsActOf Xo.univ.t.act.act ρC ∧ (∀ e, Tied 𝔐 _ y₀ (MC.pt e) (MU.pt e)) ∧
      (∀ x, x ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range) ∧
      ∀ (σ : 𝓞 E →+* V) (n : ℕ) (x : Fin n → Fin g → L), LinearIndependent L x →
        Submodule.span V (Set.range x) =
          𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V →
        IsIntFrame m m' ((algebraMap V L).comp σ) (fun k => MU.pt (x k))

def FibSandwich : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (p : Nat.Primes) (j : L →+* ℂ_[p]) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (g : ℕ)
    (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
    (ρC : 𝓞 E →+* Module.End L (Fin g → L)) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* V)
    (b : Fin (labelRk D s) → 𝔐.Li),
    (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) → MC.IsActOf 𝔐.t.act.act ρC →
    (∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ →
    ∃ x : Fin (labelRk D s) → Fin g → L,
      (∀ k, 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (b k) (MC.pt (x k))) ∧
      ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → Submodule.span V (Set.range x) =
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V) ∧
      ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ (κ : Ω) (κz : V), HT.Sandwich 𝔐 p κ → ValAt 𝔐.ξ z κ κz →
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V ≤
          Submodule.span V (Set.range x) ∧
        ∀ d : 𝓞 E, (s.isLeft → d ∈ differentIdeal ℤ (𝓞 E)) → ∀ w ∈ Submodule.span V (Set.range x),
          (κz * σ d) • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V)

def LocalCmp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω) (φ : FrameFn Xo c)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p])
    (π : F') (m : ℕ) (k : ℤ) (t : ℝ),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → d₁ ≠ 0 → d₂ ≠ 0 →
    a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) → b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) →
    a' ≠ 0 → b' ≠ 0 → ψ.comp ι = 𝔐.cst → π ≠ 0 → 0 < m →
    (∀ x : Cpt 𝔐.ξ, (∀ u : F', ‖κ' u‖ ≤ 1 → ψ u ∈ regAt 𝔐.ξ x) →
      OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (d₁ / d₂) (ψ π) m k x) →
    HasFinNorm U τ.1 φ p (κ'.comp ι) t →
    ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → (k : ℝ) / m * Real.log ‖κ' π‖ = t) ∧
    ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ κ : Ω, HT.IsCp p κ → HT.Sandwich 𝔐 p κ →
      ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(k : ℝ) / m * Real.log ‖κ' π‖ - t| ≤
        ((D.p + D.q : ℕ) : ℝ) * (cP p * Real.log (p : ℕ) - Real.log ‖κ' (ι (tauIn c τ.1 d))‖))

def ChiEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d], ∃ χ : DirichletCharacter ℂ H.d,
    GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H

def Numerics : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) (F F' : Type) [Field F] [NumberField F]
    [Field F'] [NumberField F'] (ι : F →+* F') (σ : 𝓞 E →+* F) (N : LogNorms F)
    (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (bad : Finset ℕ), Function.Injective σ → 2 ∈ bad → (∀ ℓ ∈ bad, ℓ.Prime) →
    N.IsAdelic → N.deg = ((p : ℝ) - q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) →
    (∀ (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      (∀ a : F', v.valuation F' a ≤ 1 ↔ ‖κ' a‖ ≤ 1) → v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ((ℓ : ℕ) ∉ bad → (r v : ℝ) * Real.log ‖κ' π‖ = N.fin ℓ (κ'.comp ι)) ∧
      ((ℓ : ℕ) ∈ bad → ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(r v : ℝ) * Real.log ‖κ' π‖ - N.fin ℓ (κ'.comp ι)| ≤
        ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) - Real.log ‖κ' (ι (σ d))‖))) →
    NearRecord (p + q) bad (hostRd E) (hostLval H)
      (((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
        (Module.finrank ℚ F' : ℝ))

end RootFieldNumerics.RF
