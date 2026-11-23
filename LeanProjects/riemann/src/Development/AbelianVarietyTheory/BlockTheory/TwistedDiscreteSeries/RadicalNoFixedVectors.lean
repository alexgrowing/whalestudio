import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

def radical (k : Type) [CommRing k] (r a : ℕ) : Set (GL (Fin r) k) :=
  {u | ∀ i j : Fin r, (u : Matrix (Fin r) (Fin r) k) i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j → i.val < a ∧ a ≤ j.val}

def NoFixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) : Prop :=
  ∀ x : V, (∀ u ∈ S, τ u x = x) → x = 0

def HypH {P : Type} {k : P → Type} [∀ v, CommRing (k v)] {r : ℕ} {V : P → Type} [∀ v, AddCommGroup (V v)]
    [∀ v, Module ℂ (V v)] (τ : ∀ v, Representation ℂ (GL (Fin r) (k v)) (V v)) : Prop :=
  ∀ a : ℕ, 0 < a → a < r → ∃ v, NoFixed (τ v) (radical (k v) r a)

def IsSubrep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G V) (π : Representation ℂ G W) : Prop :=
  ∃ T : V →ₗ[ℂ] W, Function.Injective T ∧ ∀ t : G, T ∘ₗ τ t = π t ∘ₗ T

def InSeries {g : ℕ} [Fact g.Prime] (ω : Fbar g →*₀ ℂ) {r : ℕ} (f : (ZMod g)[X]) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin r) (ZMod g)) V) : Prop :=
  τ.IsIrreducible ∧
  ∃ (b : Fin r → ℕ) (φ : ℕ → (ZMod g)[X]) (x : ℕ → Fbar g) (n : ℕ)
    (ρ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)),
    (∀ c ∈ Finset.univ.image b, (φ c).Monic ∧ Irreducible (φ c) ∧
      (φ c).natDegree = Fintype.card {i : Fin r // b i = c} ∧ x c ∈ rootsBar (φ c) ∧ x c ≠ 0) ∧
    f = ∏ c ∈ Finset.univ.image b, φ c ∧
    IsCuspDatum b ρ ∧
    (∀ p, ρ.character p = ∏ c ∈ Finset.univ.image b, cuspVal ω (x c) (blkMat b c p)) ∧
    IsSubrep τ (parInd b ρ)

def readAt {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} [∀ i, Fact (gp i).Prime] {pb : Fin 2 → 𝓞 E}
    (hT : IsTypeDatum gp pb) {r : ℕ} (i : Fin 2) (v : ↥(primesOf (pb i))) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin r) (kP v.1)) V) : Representation ℂ (GL (Fin r) (ZMod (gp i))) V :=
  MonoidHom.comp τ (Matrix.GeneralLinearGroup.map (resIso hT i v : ZMod (gp i) →+* kP v.1))

def FixedVectorBlocks : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (b : Fin r → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (blockTri (κ := k) b) W), IsCuspDatum b ρ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin r) k) V), IsSubrep τ (parInd b ρ) →
    ∀ a : ℕ, 0 < a → a < r → ¬ NoFixed τ (radical k r a) →
      ∃ J ⊆ Finset.univ.image b, a = ∑ c ∈ J, Fintype.card {i : Fin r // b i = c}

def FixedVectorDivisor : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (ω : Fbar g →*₀ ℂ), Function.Injective ω →
    ∀ (r : ℕ) (f : (ZMod g)[X]) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin r) (ZMod g)) V),
      InSeries ω f τ → ∀ a : ℕ, 0 < a → a < r → ¬ NoFixed τ (radical (ZMod g) r a) →
        ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = a

def HypHOfNoDivisor : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (ω : Fbar g →*₀ ℂ), Function.Injective ω →
    ∀ (r : ℕ) (P : Type) (f : P → (ZMod g)[X]) (V : P → Type) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
      (τ : ∀ v, Representation ℂ (GL (Fin r) (ZMod g)) (V v)), (∀ v, InSeries ω (f v) (τ v)) →
      (∀ a : ℕ, 1 ≤ a → 2 * a ≤ r → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a) →
      HypH (k := fun _ => ZMod g) τ

def GoodTupleHypH : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E)
    (hT : IsTypeDatum gp pb) (r m : ℕ) (K : Type) [Field K] (σ : K →+* ℂ)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (ω : ∀ i, Fbar (gp i) →*₀ ℂ), (∀ i, Function.Injective (ω i)) →
    ∀ (f : ∀ i, ↥(primesOf (pb i)) → (ZMod (gp i))[X]), IsGoodTuple hT r m σ χ ω f →
    ∀ (V : ∀ i, ↥(primesOf (pb i)) → Type) [∀ i v, AddCommGroup (V i v)] [∀ i v, Module ℂ (V i v)]
      (τ : ∀ i (v : ↥(primesOf (pb i))), Representation ℂ (GL (Fin r) (kP v.1)) (V i v)),
      (∀ i v, InSeries (ω i) (f i v) (readAt hT i v (τ i v))) →
      HypH (k := fun v : ↥(primesOf (pb 0)) => kP v.1) (τ 0)

open Classical in

def GoodCharHypH : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E)
    (hT : IsTypeDatum gp pb) (r m : ℕ) (K : Type) [Field K] (σ : K →+* ℂ)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (ω : ∀ i, Fbar (gp i) →*₀ ℂ), (∀ i, Function.Injective (ω i)) →
    ∀ Xg : Finset (G0 (primesOf (pb 0 * pb 1)) r → K), (∀ c ∈ Xg, (fun t => σ (c t)) ∈ goodChars hT r m σ χ ω) →
    ∀ c ∈ Xg, ∀ (n : ℕ) (τ : Representation ℂ (G0 (primesOf (pb 0 * pb 1)) r) (Fin n → ℂ)),
      (∀ t, τ.character t = σ (c t)) →
      ∀ a : ℕ, 0 < a → a < r → ∃ v : ↥(primesOf (pb 0)),
        NoFixed τ ((fun u => (Pi.mulSingle (toBoth hT 0 v) u : G0 (primesOf (pb 0 * pb 1)) r)) ''
          radical (kP (toBoth hT 0 v).1) r a)

example (P : Type) (k : Type) [Field k] (r : ℕ) (hr : 2 ≤ r) :
    ¬ HypH (k := fun _ : P => k) (fun _ => Representation.trivial ℂ (GL (Fin r) k) ℂ) := by
  intro h
  obtain ⟨v, hv⟩ := h 1 one_pos hr
  exact one_ne_zero (hv 1 fun _ _ => rfl)

example (k : Type) [Field k] (u : GL (Fin 2) k) : u ∈ radical k 2 1 ↔
    (u : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 ∧ (u : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
      (u : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by
  simp [radical, Fin.forall_fin_two]

end GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors
