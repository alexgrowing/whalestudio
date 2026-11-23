import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum)

section Points

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

def fnField (y : (Σ b, ι b) → Ω) : IntermediateField k Ω :=
  IntermediateField.adjoin k {t | ∃ p q : Σ b, ι b, p.1 = q.1 ∧ t = y p / y q}

open Classical in

def inum (y : (Σ b, ι b) → Ω) {n : ℕ} (a : Fin n → K → ℤ) : ℤ := intNum k (pointIdeal k y) a

def num (y : (Σ b, ι b) → Ω) {n : ℕ} (a : Fin n → K → ℤ) : ℤ := (Module.finrank (fnField k y) Ω : ℤ) * inum k y a

def IsPt (y : (Σ b, ι b) → Ω) (d : ℕ) : Prop :=
  (∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) ∧ FiniteDimensional (fnField k y) Ω ∧ Algebra.trdeg k Ω = d

def vdeg (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (a : K → ℤ) : O.ValueGroup :=
  ∏ b, (Finset.univ.sup fun i => O.valuation (y ⟨b, i⟩)) ^ a b

def ValEq (y : (Σ b, ι b) → Ω) (a : K → ℤ) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : Prop :=
  ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ O : ValuationSubring Ω, (∀ x : k, algebraMap k Ω x ∈ O) → vdeg O y a = O.valuation ρ * vdeg O y' a'

variable {k}

def joinPt (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : (Σ b : K ⊕ K', Sum.elim ι ι' b) → Ω
  | ⟨.inl b, i⟩ => y ⟨b, i⟩
  | ⟨.inr b, i⟩ => y' ⟨b, i⟩

end Points

section Flags

variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}

def IsGenU (k : Type) [Field k] [Algebra k Ω] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (d : ℕ) : Prop :=
  (∀ s m, u s m m = 1) ∧ (∀ s l m, l < m → u s l m = 0) ∧
    AlgebraicIndependent k (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    0 < d ∧ Module.finrank (IntermediateField.adjoin k
      (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2)) Ω = d

abbrev PlIx (r : S → ℕ) (b : Σ s, Fin (r s)) : Type := Fin (b.2 + 1) → Fin (r b.1)

def plPt (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) : (Σ b : (Σ s, Fin (r s)), PlIx r b) → Ω := fun x =>
  Matrix.det (Matrix.of fun a b : Fin (x.1.2 + 1) => u x.1.1 (x.2 a) (Fin.castLE x.1.2.2 b))

open Classical in

def plDeg (b : Σ s, Fin (r s)) : (Σ s, Fin (r s)) → ℤ := fun b' => if b' = b then -1 else 0

variable {Ψ : Type} {p q : ℕ} {K : Type}

abbrev rk (Ψ : Type) (p q : ℕ) : Ψ ⊕ Ψ → ℕ := Sum.elim (fun _ => p) (fun _ => q)

def grDeg (x : Ψ × Fin (p + q) → K → ℤ) : ∀ s, Fin (rk Ψ p q s) → K → ℤ
  | .inl τ, m => x (τ, ⟨m, by have : (m : ℕ) < p := m.2; omega⟩)
  | .inr τ, m => -x (τ, ⟨p + q - 1 - m, by have : (m : ℕ) < q := m.2; omega⟩)

def stepDeg (x : Ψ × Fin (p + q) → K → ℤ) (s : Ψ ⊕ Ψ) (m : Fin (rk Ψ p q s)) : K → ℤ := ∑ m' ∈ Finset.Iic m, grDeg x s m'

abbrev PairIx (Ψ : Type) (p q : ℕ) : Type :=
  Ψ × {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)}

def fibDeg (x : Ψ × Fin (p + q) → K → ℤ) (t : PairIx Ψ p q) : K → ℤ := x (t.1, t.2.1.2) - x (t.1, t.2.1.1)

def muDeg [Fintype Ψ] (x : Ψ × Fin (p + q) → K → ℤ) : K → ℤ :=
  ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i)

end Flags

def Dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (ξ : Sp Ω ⟶ X)
    (q : Cpt ξ) : Prop :=
  (∀ a ∈ regAt ξ q, i a ∈ O) ∧ ∀ a ∈ regAt ξ q, a ≠ 0 → (i a)⁻¹ ∈ O → a⁻¹ ∈ regAt ξ q

open Classical in

def PtDim : Prop :=
  ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ b, Fintype (ι b)]
    (y : (Σ b, ι b) → Ω) (d : ℕ), IsPt k y d →
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal k y) ∧
      GroundTheory.Heights₂.Heights.FieldNumbers.relDim (pointIdeal k y) = d ∧ AI.I1.IsProjVarF (pointIdeal k y) d

def NumPull : Prop :=
  ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ b, Fintype (ι b)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ b, Fintype (ι' b)] (κ : K → K') (v : (Σ b, ι b) → Σ b, ι' b)
    (y : (Σ b, ι' b) → Ω) (d : ℕ) (a : Fin d → K → ℤ), AI.I1.IsBlockMap κ v → IsPt k y d → IsPt k (y ∘ v) d →
    num k y (fun j => AI.I1.pullDeg κ (a j)) = num k (y ∘ v) a

def UnitZero : Prop :=
  ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ b, Fintype (ι b)]
    (y : (Σ b, ι b) → Ω) (n : ℕ) (a : Fin n → K → ℤ) (b : K → ℤ), IsPt k y (n + 1) → fnField k y = ⊤ → ValEq k y b y 0 →
    inum k y (Fin.snoc (α := fun _ => K → ℤ) a b) = 0

def NumEq : Prop :=
  ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ b, Fintype (ι b)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ b, Fintype (ι' b)] (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (d : ℕ)
    (a : Fin d → K → ℤ) (a' : Fin d → K' → ℤ), IsPt k y d → IsPt k y' d → (∀ j, ValEq k y (a j) y' (a' j)) →
    num k y a = num k y' a'

def GeoPF : Prop :=
  PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
  ∀ (Ω₁ : Type) [Field Ω₁] [Algebra ℚ Ω₁] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra Ω₁ Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ b, Fintype (ι b)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ b, Fintype (ι' b)] (y : (Σ b, ι b) → Ω₁)
    (y' : (Σ b, ι' b) → Ω) (n r : ℕ) (a : Fin n → K → ℤ) (N : Fin r → K' → ℤ), Birational y →
    IsArithVar (mCoordIdeal y) (n + 1) → IsPt Ω₁ y' r →
    IsPt ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (n + r) ∧
      num ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')
        (Fin.append (fun j => Sum.elim (a j) (0 : K' → ℤ)) fun j => Sum.elim (0 : K → ℤ) (N j)) = num Ω₁ y' N * inum ℚ y a

def FibNum : Prop :=
  ∃ U : ℕ → ℕ → ℕ → ℤ, ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ b, Fintype (ι b)] (y : (Σ b, ι b) → Ω)
    (u : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (d r : ℕ) (x : Ψ × Fin (p + q) → K → ℤ) (e : Fin r ≃ PairIx Ψ p q),
    IsGenU k u d → IsPt k y r → (∀ s m, ValEq k y (stepDeg x s m) (plPt u) (plDeg ⟨s, m⟩)) →
    num k y (fun j => fibDeg x (e j)) = d * U (Fintype.card Ψ) p q

def TrdegU : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (u : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (d : ℕ), IsGenU k u d →
    Algebra.trdeg k Ω = Fintype.card (PairIx Ψ p q)

def TestRelabel : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), Top.testDeg Ψ N j = Top.testDeg (Fin (Fintype.card Ψ)) N j

def GeoTest : Prop :=
  PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (p q : ℕ) (M : Top.RootModel Ψ (p + q)) [Algebra ℚ M.Ω] (n r : ℕ)
    (e : Fin r ≃ PairIx Ψ p q), q ≤ p → n = Fintype.card Ψ * p * q →
    n + r = Top.dimFl Ψ (p + q) ∧
      M.geoFun (Top.toA (Top.muSmall p ^ Top.dimX Ψ (p + q) p * Top.fibClass p)) * M.δ =
        inum ℚ M.y (Fin.append (fun _ : Fin n => muDeg M.xdeg) fun j => fibDeg M.xdeg (e j))

def NumMap : Prop :=
  ∀ (Ω₂ : Type) [Field Ω₂] [Algebra ℚ Ω₂] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (i : Ω₂ →+* Ω) (K : Type) [Fintype K] (ι : K → Type)
    [∀ b, Fintype (ι b)] (y : (Σ b, ι b) → Ω₂) (d : ℕ), Birational y → IsArithVar (mCoordIdeal y) (d + 1) →
    0 < Module.finrank i.fieldRange Ω →
    IsPt ℚ (fun x => i (y x)) d ∧ (∀ (k : Type) [Field k] [Algebra k Ω], FiniteDimensional (fnField k fun x => i (y x)) Ω) ∧
      (∀ a : Fin d → K → ℤ, num ℚ (fun x => i (y x)) a = Module.finrank i.fieldRange Ω * inum ℚ y a) ∧
      ∀ a : K → ℤ, inum ℚ y (fun _ : Fin d => a) = GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg (mCoordIdeal y) d a

def MuMass : Prop :=
  Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E)
    (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (_ : CptOrigin Y S₀ Dc Hd),
    IsFullIntersectionSystem II →
    degMu Hd = GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg (mCoordIdeal Dc.y) Dc.n Hd.aMu

def FieldJoin : Prop :=
  ∀ (Ω₀ Ω₁ Ω₂ : Type) [Field Ω₀] [Field Ω₁] [Field Ω₂] [Algebra Ω₀ Ω₁] [Algebra Ω₀ Ω₂] (S : Type) [Finite S] (r : S → ℕ)
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω₂) (d₂ e : ℕ), IsGenU Ω₀ u d₂ → 0 < e → Module.finrank Ω₀ Ω₁ = e →
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra Ω₁ Ω) (i : Ω₂ →+* Ω) (d n : ℕ),
      i.comp (algebraMap Ω₀ Ω₂) = (algebraMap Ω₁ Ω).comp (algebraMap Ω₀ Ω₁) ∧ IsGenU Ω₁ (fun s => (u s).map i) d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e

def GenIso : Prop :=
  ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X), IsCptGen ξ → IsCptGen ξ' →
    genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, ξ = spMap ψ.toRingHom ≫ ξ'

def ChartVal : Prop :=
  ∀ (X : Scheme.{0}) (Ω Ω₃ : Type) [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (ξ : Sp Ω ⟶ X) (q : Cpt ξ)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ch : ∀ k, J k) (a : K → ℤ), Dom O i ξ q →
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q →
    vdeg O (fun x => i (y x)) a = O.valuation (i (∏ k, y ⟨k, ch k⟩ ^ a k))

def Centre : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S' : Finset ℕ) (Ω Ω' Ω₃ : Type) [Field Ω] [Field Ω'] [Field Ω₃] (K K' : Type)
    [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω)
    (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y) (𝔐' : HodgeCpt Y S' y') (i : Ω →+* Ω₃) (i' : Ω' →+* Ω₃) (O : ValuationSubring Ω₃),
    spMap i ≫ 𝔐.ξ ≫ 𝔐.f = spMap i' ≫ 𝔐'.ξ ≫ 𝔐'.f →
    ∃ (q : Cpt 𝔐.ξ) (q' : Cpt 𝔐'.ξ), Dom O i 𝔐.ξ q ∧ Dom O i' 𝔐'.ξ q' ∧ 𝔐.f q.1 = 𝔐'.f q'.1

def CoordLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S' : Finset ℕ) (Ω' : Type) [Field Ω'] (K' : Type) [Fintype K'] (J' : K' → Type)
    [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω') (𝔐' : HodgeCpt Y S' y') (Fl : 𝔐'.Flag) (b : ∀ s, Fin (labelRk D s) → Fl.Li₀),
    (∀ s, LinearIndependent 𝔐'.Ω₀ (b s) ∧ Submodule.span 𝔐'.Ω₀ (Set.range (b s)) = Fl.V₀ s) →
    ∃ A : ∀ s, Y.X → Set (Fin (labelRk D s) → 𝔐'.Ω₀),
      (∀ q : Cpt 𝔐'.ξ, (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐'.ξ p q) → ∀ s, 𝔐'.V s q = Submodule.span (regAt 𝔐'.ξ q)
        {w | ∃ a ∈ A s (𝔐'.f q.1), w = ∑ m, 𝔐'.fn (a m) • Fl.j (b s m)}) ∧
      (∀ s, LinearIndependent Ω' (fun m => Fl.j (b s m)) ∧
        Submodule.span Ω' (Set.range fun m => Fl.j (b s m)) = 𝔐'.Vgen s) ∧
      ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
        (𝔐 : HodgeCpt Y S y) (ψ : 𝔐'.Ω₀ →+* Ω), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐'.ξ₀ 𝔐.f ψ →
        ∃ b₁ : ∀ s, Fin (labelRk D s) → 𝔐.Li,
          (∀ s, LinearIndependent Ω (b₁ s) ∧ Submodule.span Ω (Set.range (b₁ s)) = 𝔐.Vgen s) ∧
          ∀ q : Cpt 𝔐.ξ, (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q)
            {w | ∃ a ∈ A s (𝔐.f q.1), w = ∑ m, ψ (a m) • b₁ s m}

def FibLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S' : Finset ℕ) (Ω' : Type) [Field Ω'] (K' : Type) [Fintype K'] (J' : K' → Type)
    [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω') (𝔐' : HodgeCpt Y S' y') (Fl : 𝔐'.Flag)
    (x : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω') (b : ∀ s, Fin (labelRk D s) → Fl.Li₀)
    (u : ∀ s, Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) Ω') (k : Type) [Field k] [CharZero k] (Ω₃ : Type) [Field Ω₃]
    [Algebra k Ω₃] (i : Ω' →+* Ω₃), Fl.RootLines x e →
    (∀ s, LinearIndependent 𝔐'.Ω₀ (b s) ∧ Submodule.span 𝔐'.Ω₀ (Set.range (b s)) = Fl.V₀ s) →
    (∀ s m, u s m m = 1) → (∀ s l m, l < m → u s l m = 0) →
    (∀ s m, flagStep Ω' (Fl.b s) m = flagStep Ω' (fun m' => ∑ l, u s l m' • Fl.j (b s l)) m) →
    (∀ a, i (𝔐'.fn a) ∈ (algebraMap k Ω₃).range) →
    ∀ s m, ValEq k (fun t => i (y' t)) (stepDeg x s m) (plPt fun s => (u s).map i) (plDeg ⟨s, m⟩)

def MuLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (S' : Finset ℕ) (Ω' : Type) [Field Ω'] (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω')
    (𝔐' : HodgeCpt Y S' y') (Fl : 𝔐'.Flag) (x : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω')
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (ψ : 𝔐'.Ω₀ →+* Ω) (Ω₃ : Type) [Field Ω₃] [Algebra ℚ Ω₃]
    (i₁ : Ω →+* Ω₃) (i₂ : Ω' →+* Ω₃), Fl.RootLines x e → Or.bg = Sum.inl → Or.sm = Sum.inr → Dc.S = ∅ →
    GlobalTheory.CompanionTheory.Ar.Dominates Or.𝔐.ξ 𝔐'.ξ₀ Or.𝔐.f ψ → i₁.comp ψ = i₂.comp 𝔐'.fn →
    ValEq ℚ (fun t => i₂ (y' t)) (muDeg x) (fun t => i₁ (Dc.y t)) Hd.aMu

end SheetDecomposition
