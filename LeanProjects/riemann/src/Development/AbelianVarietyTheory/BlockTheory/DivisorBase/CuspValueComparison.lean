import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

section OnePrime

variable {g : ℕ} [Fact g.Prime]

def rootC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def labelChar (ω : Fbar g →*₀ ℂ) (d : ℕ) (x y : Fbar g) : ℂ :=
  ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}

open Classical in

def cuspVal (ω : Fbar g →*₀ ℂ) (x : Fbar g) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) : ℂ :=
  if ∃ (p : (ZMod g)[X]) (k : ℕ), Irreducible p ∧ M.charpoly = p ^ k then
    (-1) ^ (Fintype.card ι - 1) *
      ∑ y ∈ (rootsBar M.charpoly).toFinset, labelChar ω (Fintype.card ι) x y *
        ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) y)),
          (1 - (g : ℂ) ^ ((rootsBar M.charpoly).toFinset.card * i))
  else 0

def IsTypeChar (ω : Fbar g →*₀ ℂ) {r : ℕ} (f : (ZMod g)[X]) (χ : GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (φ : ℕ → (ZMod g)[X]) (x : ℕ → Fbar g) (n : ℕ)
    (ρ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)),
    (∀ c ∈ Finset.univ.image b, (φ c).Monic ∧ Irreducible (φ c) ∧
      (φ c).natDegree = Fintype.card {a : Fin r // b a = c} ∧ x c ∈ rootsBar (φ c)) ∧
    f = ∏ c ∈ Finset.univ.image b, φ c ∧
    IsCuspDatum b ρ ∧
    (∀ p, ρ.character p = ∏ c ∈ Finset.univ.image b, cuspVal ω (x c) (blkMat b c p)) ∧
    ∀ y, χ y = (parInd b ρ).character y

def IsTameLabel (ω : Fbar g →*₀ ℂ) (η : (ZMod g)ˣ → ℂ) (c : (ZMod g)ˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, η z =
    labelChar ω 1 (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) (algebraMap (ZMod g) (Fbar g) (z : ZMod g))

theorem labelChar_one_right (ω : Fbar g →*₀ ℂ) (d : ℕ) (x : Fbar g) : labelChar ω d x 1 = 1 := by
  have : sInf {a : ℕ | ω 1 = rootC (g ^ d - 1) ^ a} = 0 := by
    rw [Nat.sInf_eq_zero]; left; simp
  rw [labelChar, this, pow_zero]

example (ω : Fbar g →*₀ ℂ) : IsTameLabel ω (fun _ => 1) 1 := by
  intro z; simp [labelChar]

end OnePrime

section BothPrimes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

theorem pb_ne_zero (hT : IsTypeDatum gp pb) (i : Fin 2) : pb i ≠ 0 := by
  intro h
  have h1 := hT.norm i
  rw [h] at h1
  have h2 : (gp i : E) = 0 := by rw [← h1]; simp
  exact (hT.prime i).ne_zero (by exact_mod_cast h2)

def toBoth (hT : IsTypeDatum gp pb) (i : Fin 2) (v : ↥(primesOf (pb i))) : ↥(primesOf (pb 0 * pb 1)) :=
  ⟨v.1, mem_primesOf.2 ⟨mul_ne_zero (pb_ne_zero hT 0) (pb_ne_zero hT 1), by
    have hv := (mem_primesOf.1 v.2).2
    fin_cases i
    · exact Ideal.mul_mem_right _ _ hv
    · exact Ideal.mul_mem_left _ _ hv⟩⟩

def resIso (hT : IsTypeDatum gp pb) (i : Fin 2) (v : ↥(primesOf (pb i))) : ZMod (gp i) ≃+* kP v.1 :=
  have hc : Nat.card (kP v.1) = gp i := hT.deg1 i v.1 (mem_primesOf.1 v.2).2
  have : Finite (kP v.1) := Nat.finite_of_card_ne_zero (by rw [hc]; exact (hT.prime i).ne_zero)
  letI : Fintype (kP v.1) := Fintype.ofFinite _
  ZMod.ringEquivOfPrime (kP v.1) (hT.prime i) (by rw [← Nat.card_eq_fintype_card, hc])

def compAt (hT : IsTypeDatum gp pb) {r : ℕ} (i : Fin 2) (v : ↥(primesOf (pb i)))
    (t : G0 (primesOf (pb 0 * pb 1)) r) : GL (Fin r) (ZMod (gp i)) :=
  Matrix.GeneralLinearGroup.map ((resIso hT i v).symm : kP v.1 →+* ZMod (gp i)) (t (toBoth hT i v))

variable [∀ i, Fact (gp i).Prime] {K : Type} [Field K]

def IsGoodTuple (hT : IsTypeDatum gp pb) (r m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ)
    (ω : ∀ i, Fbar (gp i) →*₀ ℂ) (f : ∀ i, ↥(primesOf (pb i)) → (ZMod (gp i))[X]) : Prop :=
  ∀ i, ∃ c : ↥(primesOf (pb i)) → Fin m → (ZMod (gp i))ˣ,
    (∀ v j, IsTameLabel (ω i)
      (fun z => σ (χ (j.val + 1) v.1 (Units.map ((resIso hT i v : ZMod (gp i) →+* kP v.1) : ZMod (gp i) →* kP v.1) z) : Kˣ))
      (c v j)) ∧
    IsGood r (gp i) (f i) fun v (js : Fin m × Bool) => if js.2 then c v js.1 else (c v js.1)⁻¹

def goodChars (hT : IsTypeDatum gp pb) (r m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ)
    (ω : ∀ i, Fbar (gp i) →*₀ ℂ) : Set (G0 (primesOf (pb 0 * pb 1)) r → ℂ) :=
  {Θ | ∃ (f : ∀ i, ↥(primesOf (pb i)) → (ZMod (gp i))[X])
      (τ : ∀ i, ↥(primesOf (pb i)) → GL (Fin r) (ZMod (gp i)) → ℂ),
    IsGoodTuple hT r m σ χ ω f ∧ (∀ i v, IsTypeChar (ω i) (f i v) (τ i v)) ∧
    ∀ t, Θ t = ∏ i, ∏ v, τ i v (compAt hT i v t)}

end BothPrimes

def GoodCharsRealised : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E)
    (hT : IsTypeDatum gp pb) (r m : ℕ) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (ω : ∀ i, Fbar (gp i) →*₀ ℂ),
    (∀ i, Function.Injective (ω i)) →
    (∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (G0 (primesOf (pb 0 * pb 1)) r))) →
    (∀ Θ ∈ goodChars hT r m σ χ ω, ∃ ΘK : G0 (primesOf (pb 0 * pb 1)) r → K,
      (∀ t, σ (ΘK t) = Θ t) ∧ IsAbsIrrChar ΘK) ∧
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 (primesOf (pb 0 * pb 1)) r),
      (Set.range fun (s : T.S) (t : G0 (primesOf (pb 0 * pb 1)) r) => σ (LinearMap.trace K (T.W s) (T.tau s t))) =
        goodChars hT r m σ χ ω

end GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison
