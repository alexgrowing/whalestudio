import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X X₀ : Scheme.{0}}
  {t : SAB H X} (t₀ : SAB H X₀) (φ : t₀.G.left ⟶ t.G.left)

def Gens {O : Type} [CommRing O] {x : Sp O ⟶ X} {q N : ℕ} (c : Fin N → TorsChar t x q) : Prop :=
  ∀ c' : TorsChar t x q, ∃ n : Fin N → ℕ, ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
    (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G), w ^ q = 1 → c'.χ B w = ∏ m, (c m).χ B w ^ n m

def Isotropic {p : ℕ} [Fact p.Prime] {x : Sp ↥(intO ℂ_[p]) ⟶ X} {N : ℕ} (c : Fin N → TorsChar t x (p ^ 2))
    (J : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (h : Fin N → Fin g → ↥(intO ℂ_[p])),
    IsTanBasis t x e → (∀ m, DlogIs t p 2 (c m) e (h m)) → ∀ a a' : Fin g → ℂ_[p],
    (∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1) → (∀ i, ‖(p : ℂ_[p]) * a' i‖ ≤ 1) →
    (∀ m, ‖∑ i, (h m i : ℂ_[p]) * a i‖ ≤ 1) → (∀ m, ‖∑ i, (h m i : ℂ_[p]) * a' i‖ ≤ 1) →
    ‖∑ m, ∑ m', (J m m' : ℂ_[p]) * ((∑ i, (h m i : ℂ_[p]) * a i) * ∑ i, (h m' i : ℂ_[p]) * a' i)‖ < 1

def IsGram {k : Type} [CommRing k] {x : Sp k ⟶ X₀} (q : ℕ) {N : ℕ} (s : Fin N → (Over.mk x ⟶ t₀.G)) (ζ : kˣ)
    (B : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  (∀ m, s m ^ q = 1) ∧ ∀ m m', Out.WeilIs t₀.G t₀.PP.L (q : ℤ) (s m) (s m') (unitOn (ζ ^ B m m'))

def IsWeilHom {K : Type} [Field K] {ξ₀ : Sp K ⟶ X₀} {ξ : Sp K ⟶ X} {q : ℕ} (s : Over.mk ξ₀ ⟶ t₀.G)
    (χ : TorsK t ξ q →* Kˣ) : Prop :=
  ∀ (k : TorsK t ξ q) (a : Over.mk ξ₀ ⟶ t₀.G), a.left ≫ φ = k.1.left →
    Out.WeilIs t₀.G t₀.PP.L (q : ℤ) a s (unitOn (χ k))

def IsWeilChar {p : ℕ} [Fact p.Prime] {z : Sp ↥(intO ℂ_[p]) ⟶ X} {yy : Sp ℂ_[p] ⟶ X₀} {q : ℕ}
    (s : Over.mk yy ⟶ t₀.G) (c : TorsChar t z q) : Prop :=
  ∀ (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ z) ⟶ t.G) (a : Over.mk yy ⟶ t₀.G), w ^ q = 1 →
    a.left ≫ φ = spMap (intO ℂ_[p]).subtype ≫ w.left →
    Out.WeilIs t₀.G t₀.PP.L (q : ℤ) a s (unitOn (Units.map (intO ℂ_[p]).subtype.toMonoidHom (c.χ _ w)))

def HasPoint {p : ℕ} [Fact p.Prime] (z : Sp ↥(intO ℂ_[p]) ⟶ X) (yy : Sp ℂ_[p] ⟶ X₀) : Prop :=
  ∃ (v : Valuation ℂ_[p] ℝ≥0) (Λ : Type) (_ : CommRing Λ) (_ : StarRing Λ) (P : GlobalTheory.HTLat.Point p v ↥(intO ℂ_[p]) Λ)
    (π : P.G.left ⟶ t.G.left) (ψ : P.A.A.left ⟶ t₀.G.left), IsGrpPullback P.G t.G z π ∧ IsGrpPullback P.A.A t₀.G yy ψ ∧
    ψ ≫ φ = P.gen ≫ π ∧ LBIso P.A.L (t₀.PP.L.pull ψ)

def ChartDlog {S : Scheme.{0}} {ρ : S ⟶ X} {p : ℕ} [Fact p.Prime] {N : ℕ}
    (c : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar t (y ≫ ρ) (p ^ 2)) {U : S.Opens} (hU : IsAffineOpen U) {g : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(S, U)) : Prop :=
  ∀ (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S), spMap x ≫ hU.fromSpec = y →
    ∀ j, DlogIs t p 2 (c j y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def ChartVal (V : Cover Y) (ρ' : V.X ⟶ X) {m N : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn)
    {U : V.X.Opens} (hU : IsAffineOpen U) {g : ℕ} (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left))
    (h : Fin N → Fin g → Γ(V.X, U)) (M : Matrix (Fin N) (Fin m) V.G.functionField) : Prop :=
  ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z),
    spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧
    (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l)
      (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧
    ∀ r l, (M * ((T (V.π z)).map V.φ)⁻¹) r l =
      algebraMap (V.G.presheaf.stalk z) V.G.functionField (∑ i, α (h r i) * a l i)

variable (t) in

def wedgeNorm {p : ℕ} [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left))
    (k : ℕ) : ℝ :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin m => (l : ℕ) < k), GlobalTheory.ShFam.Pad.grNorm t x (latHT t p x) u l

end Defs

def Clauses {K : Type} [Field K] (w : K → ℝ) {g : ℕ} (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (ν : ℕ → ℝ)
    (M M' : Matrix (Fin (g + g)) (Fin g) K) : Prop :=
  (∀ (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin (g + g)), w (minorAt M k hk σ) ≤ ν k) ∧
  (∀ (k : ℕ) (hk : k ≤ g), ∃ σ : Fin k → Fin (g + g), w (minorAt M k hk σ) = ν k) ∧
  (∀ u u' : Fin g → K, (∀ r, w (M.mulVec u r) ≤ 1) → (∀ r, w (M.mulVec u' r) ≤ 1) →
    w (dotProduct (M.mulVec u) ((J.map (Int.castRingHom K)).mulVec (M.mulVec u'))) < 1) ∧
  ∀ u : Fin g → K, (∀ r, w (M.mulVec u r) ≤ 1) → ∀ r, w (M'.mulVec u r - M.mulVec u r) < 1

def GramSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] [CharZero K] (ξ₀ : Sp K ⟶ Xo.XF c) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) →
    SplitK Z.t (ξ₀ ≫ Z.j) q → ∀ N : ℕ, N = Module.finrank ℤ Dw.La →
    ∃ (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ) (B : Matrix (Fin N) (Fin N) ℤ), IsPrimitiveRoot ζ q ∧ IsUnit B.det ∧
      IsGram Z.oF.t q s ζ B ∧ ∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m

def HomSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] (ξ₀ : Sp K ⟶ Xo.XF c) (ξ : Sp K ⟶ Z.X), ξ₀ ≫ Z.j = ξ → ∀ q : ℕ, q ≠ 0 →
    ∀ (N : ℕ) (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ) (B : Matrix (Fin N) (Fin N) ℤ), IsPrimitiveRoot ζ q →
    IsUnit B.det → IsGram Z.oF.t q s ζ B → (∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) →
    ∃ χ : Fin N → (TorsK Z.t ξ q →* Kˣ), (∀ m, IsWeilHom Z.oF.t Z.m.φ (s m) (χ m)) ∧
      ∀ χ' : TorsK Z.t ξ q →* Kˣ, ∃ n : Fin N → ℕ, χ' = ∏ m, χ m ^ n m

def ExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (x₀ : Sp R ⟶ Xo.XF c) (ξ₀ : Sp K ⟶ Xo.XF c), spMap (algebraMap R K) ≫ x₀ = ξ₀ → ∀ q : ℕ, q ≠ 0 →
    ∀ s : Over.mk ξ₀ ⟶ Z.oF.t.G, s ^ q = 1 →
    ∃ s' : Over.mk x₀ ⟶ Z.oF.t.G, s' ^ q = 1 ∧ spMap (algebraMap R K) ≫ s'.left = s.left

def SpecSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (R K k : Type) [CommRing R] [CommRing K] [CommRing k] (u : R →+* K) (ψ : R →+* k), Function.Injective u →
    ∀ (x₀ : Sp R ⟶ Xo.XF c) (ξ₀ : Sp K ⟶ Xo.XF c) (y₀ : Sp k ⟶ Xo.XF c) (q : ℕ), q ≠ 0 →
    ∀ (a b : Over.mk x₀ ⟶ Z.oF.t.G) (a₁ b₁ : Over.mk ξ₀ ⟶ Z.oF.t.G) (a₂ b₂ : Over.mk y₀ ⟶ Z.oF.t.G),
    a ^ q = 1 → b ^ q = 1 → a₁.left = spMap u ≫ a.left → b₁.left = spMap u ≫ b.left →
    a₂.left = spMap ψ ≫ a.left → b₂.left = spMap ψ ≫ b.left → ∀ r : Rˣ,
    Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) a₁ b₁ (unitOn (Units.map u.toMonoidHom r)) →
    Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) a₂ b₂ (unitOn (Units.map ψ.toMonoidHom r))

def CharSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [IsLocallyNoetherian Z.X]
    (K : Type) [Field K] [CharZero K] (ξ₀ : Sp K ⟶ Xo.XF c) (ξ : Sp K ⟶ Z.X), ξ₀ ≫ Z.j = ξ → ∀ q : ℕ, q ≠ 0 →
    (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK Z.t ξ q →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (x : Sp R ⟶ Z.X), spMap (algebraMap R K) ≫ x = ξ →
    ∀ (R' : Type) [CommRing R'] (r : R →+* R') (u : R' →+* K) (x₀ : Sp R' ⟶ Xo.XF c), Function.Injective u →
    u.comp r = algebraMap R K → x₀ ≫ Z.j = spMap r ≫ x → spMap u ≫ x₀ = ξ₀ →
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (ψ' : R' →+* ℂ_[p]) (z : Sp ↥(intO ℂ_[p]) ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c), IsLocalHom ψ → ψ'.comp r = (intO ℂ_[p]).subtype.comp ψ → spMap ψ ≫ x = z →
    spMap ψ' ≫ x₀ = yy → ∀ (s : Over.mk ξ₀ ⟶ Z.oF.t.G) (s' : Over.mk x₀ ⟶ Z.oF.t.G) (s'' : Over.mk yy ⟶ Z.oF.t.G),
    s' ^ q = 1 → s.left = spMap u ≫ s'.left → s''.left = spMap ψ' ≫ s'.left →
    ∀ (χ : TorsK Z.t ξ q →* Kˣ) (ch : TorsChar Z.t z q), IsWeilHom Z.oF.t Z.m.φ s χ →
    InducedBy χ x (algebraMap R K) ψ ch → IsWeilChar Z.oF.t Z.m.φ s'' ch

def GensSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K]
    (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ →
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z →
    ∀ (N : ℕ) (χ : Fin N → (TorsK t ξ q →* Kˣ)) (ch : Fin N → TorsChar t z q),
    (∀ χ' : TorsK t ξ q →* Kˣ, ∃ n : Fin N → ℕ, χ' = ∏ m, χ m ^ n m) →
    (∀ m, InducedBy (χ m) x (algebraMap R K) ψ (ch m)) → Gens ch

def LiftSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (ψ : R →+* k), IsLocalHom ψ → ∀ (x : Sp R ⟶ Z.X)
    (yy : Sp k ⟶ Xo.XF c), spMap ψ ≫ x = yy ≫ Z.j → ∃ x₀ : Sp R ⟶ Xo.XF c, x₀ ≫ Z.j = x

def IntSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : ↥(intO ℂ_[p])) ∧ IsAdicComplete (Ideal.span {(p : ↥(intO ℂ_[p]))}) ↥(intO ℂ_[p]) ∧
    HenselianLocalRing ↥(intO ℂ_[p]) ∧ (Valued.v : Valuation ℂ_[p] ℝ≥0).Integers ↥(intO ℂ_[p]) ∧
    Nonempty (ℤ_[p] →+* ↥(intO ℂ_[p]))

def PointSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)), 1 ≤ Dw.p + Dw.q →
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (k : K →+* ℂ_[p]) (z₀ : Sp K ⟶ Xo.XF c), (∀ a : K, IsAlgebraic ℤ a) →
    ∀ (z : Sp ↥(intO ℂ_[p]) ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c), spMap k ≫ z₀ = yy →
    spMap (intO ℂ_[p]).subtype ≫ z = yy ≫ Z.j → HasPoint Z.oF.t Z.m.φ z yy

def LinSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] ℂ_[p]], (∀ x : ℤ_[p], ‖algebraMap ℤ_[p] ℂ_[p] x‖ ≤ 1) →
    ∀ (T : Type) [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (N : ℕ),
    Module.finrank ℤ_[p] T = N → ∀ (e : LinearMap.BilinForm ℤ_[p] T) (s : Fin N → T) (u : ℤ_[p]ˣ)
    (B J : Matrix (Fin N) (Fin N) ℤ), B.transpose * J = 1 → (∀ m m', (p : ℤ_[p]) ∣ e (s m) (s m') - u * (B m m' : ℤ_[p])) →
    ∀ (b b' : ℂ_[p] ⊗[ℤ_[p]] T), e.baseChange ℂ_[p] b b' = 0 → ∀ β β' : Fin N → ℂ_[p], (∀ m, ‖β m‖ ≤ 1) →
    (∀ m, ‖β' m‖ ≤ 1) → (∀ m, ‖β m - e.baseChange ℂ_[p] b (1 ⊗ₜ s m)‖ < 1) →
    (∀ m, ‖β' m - e.baseChange ℂ_[p] b' (1 ⊗ₜ s m)‖ < 1) → ‖∑ m, ∑ m', (J m m' : ℂ_[p]) * (β m * β' m')‖ < 1

def IsoSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (p : ℕ) [Fact p.Prime] (z : Sp ↥(intO ℂ_[p]) ⟶ Z.X) (yy : Sp ℂ_[p] ⟶ Xo.XF c), HasPoint Z.oF.t Z.m.φ z yy →
    ∀ N : ℕ, N = Module.finrank ℤ Dw.La → ∀ (s : Fin N → (Over.mk yy ⟶ Z.oF.t.G)) (ζ : ℂ_[p]ˣ)
    (B J : Matrix (Fin N) (Fin N) ℤ), IsPrimitiveRoot ζ (p ^ 2) → B.transpose * J = 1 → IsGram Z.oF.t (p ^ 2) s ζ B →
    ∀ ch : Fin N → TorsChar Z.t z (p ^ 2), (∀ m, IsWeilChar Z.oF.t Z.m.φ (s m) (ch m)) → Isotropic ch J

def FullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)), Gens c →
    ∃ (N' : ℕ) (c' : Fin N' → TorsChar t x (p ^ 2)) (n : Fin N' → Fin N → ℕ) (k : Fin N → Fin N'),
      (∀ c₀ : TorsChar t x (p ^ 2), ∃ j, Agree c₀ (c' j)) ∧ (∀ m, n (k m) = Pi.single m 1) ∧
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (h : Fin N → Fin g → ↥(intO ℂ_[p])),
        (∀ i, IsTanAtG t x (e i)) → (∀ m, DlogIs t p 2 (c m) e (h m)) →
        ∀ j, DlogIs t p 2 (c' j) e fun i => ∑ m, (n j m : ↥(intO ℂ_[p])) * h m i

def PtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X),
    X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (n n' : ℕ)
    (e : Fin n → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin n' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)),
    IsTanBasis t x e → IsTanBasis t x e' → ∀ (g : ℕ) (c : Fin (g + g) → TorsChar t x (p ^ 2))
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (h : Fin (g + g) → Fin n → ↥(intO ℂ_[p]))
    (h' : Fin (g + g) → Fin n' → ↥(intO ℂ_[p])), Gens c → Isotropic c J → (∀ j, DlogIs t p 2 (c j) e (h j)) →
    (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin g → Fin n → ℂ_[p])
    (a' : Fin g → Fin n' → ℂ_[p]), LinearIndependent ℂ_[p] a →
    (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) →
    (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) →
    (∀ k, 0 < wedgeNorm t (spMap (intO ℂ_[p]).subtype ≫ x) u k) ∧
    Clauses (fun b : ℂ_[p] => ‖b‖) J (wedgeNorm t (spMap (intO ℂ_[p]).subtype ≫ x) u)
      (Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i) (Matrix.of fun r l => ∑ i, (h' r i : ℂ_[p]) * a' l i)

def ConvSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (g : ℕ)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (ν : ℕ → ℝ) (M M' : Matrix (Fin (g + g)) (Fin g) (AlgebraicClosure F)),
    (∀ k, 0 < ν k) → Clauses (fun b : ℂ_[resP v] => ‖b‖) J ν (M.map (ioOf (resP v) ε)) (M'.map (ioOf (resP v) ε)) →
    Clauses (fun b => ε.w b) J (fun k => Real.exp ((-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (ν k))) M M'

def ChartSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ →
    ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left))
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn),
    (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y l)) → (∀ y, IsUnit (T y).det) →
    (∀ y i, IsCombAtG t (GlobalTheory.ShFam.genericPt Y ≫ ρ)
      (fun k => spMap (dualMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField)) ≫ f y k) (fun k => T y k i) (u₀ i)) →
    ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)),
    IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (N : ℕ) (h : Fin N → Fin g → Γ(V.X, U)),
    ∃ M : Matrix (Fin N) (Fin m) V.G.functionField, ChartVal V ρ' f T hU e h M

def TestSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X),
    X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X),
    V.j ≫ ρ' = V.π ≫ ρ → ∀ (g : ℕ) (f : ∀ y : Y.X, Fin g → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn),
    (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K),
      IsIndep t (spMap ψ ≫ GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime]
    (c : Fin (g + g) → ∀ y : Sp ↥(intO ℂ_[resP v]) ⟶ V.X, TorsChar t (y ≫ ρ') (resP v ^ 2))
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ), (∀ y, Gens fun m => c m y) →
    ∀ (U U' : V.X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (n n' : ℕ)
    (e : Fin n → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (e' : Fin n' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left))
    (h : Fin (g + g) → Fin n → Γ(V.X, U)) (h' : Fin (g + g) → Fin n' → Γ(V.X, U'))
    (M M' : Matrix (Fin (g + g)) (Fin g) V.G.functionField),
    IsTanBasis t (hU.fromSpec ≫ ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → ChartDlog c hU e h → ChartDlog c hU' e' h' →
    ChartVal V ρ' f T hU e h M → ChartVal V ρ' f T hU' e' h' M' →
    ∀ (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), z ≫ V.π = y.1 →
    spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' →
    (∀ yO : Sp ↥(intO ℂ_[resP v]) ⟶ V.X, spMap (intO ℂ_[resP v]).subtype ≫ yO = spMap (ioOf (resP v) ε) ≫ z ≫ V.j →
      Isotropic (fun m => c m yO) J) →
    ∀ ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v], ψ = (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom →
    (∀ k, 0 < wedgeNorm t (spMap ψ ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) k) ∧
    Clauses (fun b : ℂ_[resP v] => ‖b‖) J
      (wedgeNorm t (spMap ψ ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) fun l => spMap (dualMap ψ) ≫ f (below y.1) l)
      ((valMat V M (T (below y.1)) z).map (ioOf (resP v) ε)) ((valMat V M' (T (below y.1)) z).map (ioOf (resP v) ε))

def BundleSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (n : ℕ) (Δ : Fin n → Y.Dv) (φ : Fin n → PtFn Y),
    (∃ M : GlobalTheory.TrueGeo.Model Y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) → (∀ i, FromModel Y (Δ i) (eqn (Δ i)) (φ i)) →
    ∃ (V₀ : Cover Y) (m : ℕ), 0 < m ∧ ∀ (V : Cover Y) (a : V.X ⟶ V₀.X) (b : V.G ⟶ V₀.G), a ≫ V₀.p = V.p →
      V.j ≫ a = b ≫ V₀.j → b ≫ V₀.π = V.π → b (genericPoint V.G) = genericPoint V₀.G →
      ∃ L : Fin n → LB V.X, ∀ i, (L i).IsLB ∧
        ∀ p : ℕ, NormsAt V (L i) p ⊤ (fun y => genAt (Δ i) y ^ m) fun v e y => m * φ i v e y

end GlobalTheory.HalfGeo
