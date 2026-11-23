import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def GenOver (V : Cover Y) (f : Y.X → Y.Fn) (φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l : ℕ) : Prop :=
  ∃ (n : ℕ) (U : V.X → V.X.Opens) (s : V.X → Fin n → V.G.functionField), (∀ x, x ∈ U x) ∧
    (∀ x J (z : V.G), V.j z ∈ U x → RegAt z (s x J / V.φ (f (V.π z)))) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ x, ⊤ ≤ yt ⁻¹ᵁ U x →
      (∀ J, e.w (TrueGeo.valAt z (s x J / V.φ (f (below y.1)))) * Real.exp (φ v e y) ≤ 1) ∧
      (∃ J, e.w (TrueGeo.valAt z (s x J / V.φ (f (below y.1)))) * Real.exp (φ v e y) = 1) ∧
      ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → ∀ J,
        e.w (TrueGeo.valAt z ((s x J - s x' J) / V.φ (f (below y.1)))) * Real.exp (φ v e y) < 1

end Cover

def pairDet {R J : Type} [CommRing R] {g m k : ℕ} (h : J → Fin g → R) (a : Fin m → Fin g → R) (hk : k ≤ m)
    (σ : Fin k → J) : R :=
  (Matrix.of fun r l : Fin k => ∑ i, h (σ r) i * a (Fin.castLE hk l) i).det

theorem map_pairDet {R S J : Type} [CommRing R] [CommRing S] (φ : R →+* S) {g m k : ℕ} (h : J → Fin g → R)
    (a : Fin m → Fin g → R) (hk : k ≤ m) (σ : Fin k → J) :
    φ (pairDet h a hk σ) = pairDet (fun j i => φ (h j i)) (fun l i => φ (a l i)) hk σ := by
  rw [pairDet, RingHom.map_det]
  congr 1
  ext r l
  simp

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def SplitK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (io : K →+* Ω) (w : Over.mk (spMap io ≫ ξ) ⟶ t.G), w ^ q = 1 →
    ∃ w₀ : Sp K ⟶ t.G.left, spMap io ≫ w₀ = w.left

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker

variable {t} in

def Agree {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ} (c c' : TorsChar t x q) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G),
    w ^ q = 1 → c.χ B w = c'.χ B w

variable {t} in

def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

def CharFam {S : Scheme.{0}} (ρ : S ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar t (y ≫ ρ) (p ^ n)),
    (∀ y (c' : TorsChar t (y ≫ ρ) (p ^ n)), ∃ j, Agree c' (c j y)) ∧
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)),
      IsTanBasis t (R := Γ(S, U)) (hU.fromSpec ≫ ρ) e → ∃ h : Fin N → Fin g → Γ(S, U),
        ∀ (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S), spMap x ≫ hU.fromSpec = y →
          ∀ j, DlogIs t p n (c j y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))

theorem splitK_of_isAlgClosed [IsLocallyNoetherian X] {K : Type} [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ X) {q : ℕ}
    (hq : q ≠ 0) : SplitK t ξ q := by
  intro Ω _ io w hw
  let ε := (FractionRing.algEquiv K K).toRingEquiv
  have : IsAlgClosed (FractionRing K) := IsAlgClosed.of_ringEquiv K _ ε.symm
  have e : (io.comp ε.toRingHom).comp (algebraMap K (FractionRing K)) = io :=
    RingHom.ext fun a => congrArg io ((FractionRing.algEquiv K K).commutes a)
  have h := splitTors_of_isAlgClosed E H X t K ξ q hq Ω (io.comp ε.toRingHom)
  rw [e] at h
  obtain ⟨w₀, h₀⟩ := h w hw
  refine ⟨spMap ε.toRingHom ≫ w₀, ?_⟩
  rw [← h₀, ← Category.assoc, ← Spec.map_comp]
  rfl

end Chars

end GlobalTheory.HtGen
