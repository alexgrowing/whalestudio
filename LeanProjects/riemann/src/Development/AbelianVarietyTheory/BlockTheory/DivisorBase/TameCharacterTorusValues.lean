import Mathlib
import Formalism.CyclotomicNorms.StatementT
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

def rootOfOne (q d n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / ((q : ℂ) ^ d - 1))

def torusValue (q d e : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ (d - d / e) * (∏ i ∈ Finset.Ico 1 (d / e), ((q : ℂ) ^ (e * i) - 1)) *
    ∑ i ∈ Finset.range e, z ^ (n * q ^ i)

example (q n : ℕ) (z : ℂ) : torusValue q 1 1 z n = z ^ n := by simp [torusValue]

example (q d : ℕ) (z : ℂ) : torusValue q d 1 z 0 = ∏ i ∈ Finset.Ico 1 d, ((q : ℂ) ^ i - 1) := by
  simp [torusValue]

example (q n : ℕ) (z : ℂ) : torusValue q 2 2 z n = -(z ^ n + z ^ (n * q)) := by
  simp [torusValue, Finset.sum_range_succ]

section Local

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

def blkSize (b : Fin r → ℕ) (c : ℕ) : ℕ := (Finset.univ.filter fun a => b a = c).card

structure IsLabelledDatum (ι : (Fbar g)ˣ →* ℂˣ) (b : Fin r → ℕ) (fac : ℕ → (ZMod g)[X]) {n : ℕ}
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)) : Prop where
  cusp : IsCuspDatum b σ
  monic : ∀ c ∈ Finset.univ.image b, (fac c).Monic
  irred : ∀ c ∈ Finset.univ.image b, Irreducible (fac c)
  ne_X : ∀ c ∈ Finset.univ.image b, fac c ≠ X
  degree : ∀ c ∈ Finset.univ.image b, (fac c).natDegree = blkSize b c
  value : ∀ (x y : ℕ → (Fbar g)ˣ) (m : ℕ → ℕ) (p : blockTri (κ := ZMod g) b),
    (∀ c ∈ Finset.univ.image b, aeval ((x c : (Fbar g)ˣ) : Fbar g) (fac c) = 0) →
    (∀ c ∈ Finset.univ.image b,
      minpoly (ZMod g) (blkMat b c p) = minpoly (ZMod g) ((y c : (Fbar g)ˣ) : Fbar g)) →
    (∀ c ∈ Finset.univ.image b, ((ι (y c) : ℂˣ) : ℂ) = rootOfOne g (blkSize b c) (m c)) →
    σ.character p = ∏ c ∈ Finset.univ.image b,
      torusValue g (blkSize b c) (minpoly (ZMod g) ((y c : (Fbar g)ˣ) : Fbar g)).natDegree
        ((ι (x c) : ℂˣ) : ℂ) (m c)

def IsTypeChar (ι : (Fbar g)ˣ →* ℂˣ) (s : (ZMod g)[X]) (ch : GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (fac : ℕ → (ZMod g)[X]) (n : ℕ)
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)),
    IsLabelledDatum ι b fac σ ∧ s = ∏ c ∈ Finset.univ.image b, fac c ∧
      ∀ t, ch t = (parInd b σ).character t

def IsCharLabel (ι : (Fbar g)ˣ →* ℂˣ) (θ : (ZMod g)ˣ → ℂ) (a : (ZMod g)ˣ) : Prop :=
  ∀ (y : (ZMod g)ˣ) (m : ℕ),
    ((ι (Units.map (algebraMap (ZMod g) (Fbar g) : ZMod g →* Fbar g) y) : ℂˣ) : ℂ) = rootOfOne g 1 m →
    θ y = ((ι (Units.map (algebraMap (ZMod g) (Fbar g) : ZMod g →* Fbar g) a) : ℂˣ) : ℂ) ^ m

example (ι : (Fbar g)ˣ →* ℂˣ) : IsCharLabel ι (fun _ => 1) 1 := by
  intro y m _; simp

def lineRep (θ : (ZMod g)ˣ →* ℂˣ) :
    Representation ℂ (blockTri (κ := ZMod g) (fun _ : Fin 1 => 0)) (Fin 1 → ℂ) where
  toFun p := ((θ (blkDet (fun _ : Fin 1 => 0) 0 p) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by
    rw [map_one, map_one, Units.val_one, one_smul]; rfl
  map_mul' p q := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul]
    ext1 v
    ext i
    simp [mul_left_comm]

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

abbrev typePlaces (pb : Fin 2 → 𝓞 E) : Finset (Pl E) := primesOf (pb 0 * pb 1)

abbrev PlacesOver (pb : Fin 2 → 𝓞 E) (i : Fin 2) : Type :=
  {v : ↥(typePlaces pb) // pb i ∈ v.1.asIdeal}

variable {K : Type} [Field K]

def tameChar (emb : K →+* ℂ) (χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ) {m g : ℕ} (w : Pl E) (e : kP w ≃+* ZMod g)
    (j : Fin m × Bool) (y : (ZMod g)ˣ) : ℂ :=
  emb (((if j.2 then χ (j.1.val + 1) w else (χ (j.1.val + 1) w)⁻¹)
    (Units.map (e.symm : ZMod g →* kP w) y) : Kˣ) : K)

open Classical in

def goodChars (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime] (pb : Fin 2 → 𝓞 E) (r m : ℕ)
    (e : ∀ i, ∀ v : PlacesOver pb i, kP v.1.1 ≃+* ZMod (gp i))
    (ι : ∀ i, PlacesOver pb i → ((Fbar (gp i))ˣ →* ℂˣ))
    (emb : K →+* ℂ) (χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ) : Set (G0 (typePlaces pb) r → ℂ) :=
  {ch | ∃ (s : ∀ i, PlacesOver pb i → (ZMod (gp i))[X])
      (lab : ∀ i, PlacesOver pb i → Fin m × Bool → (ZMod (gp i))ˣ)
      (loc : ∀ i, PlacesOver pb i → GL (Fin r) (ZMod (gp i)) → ℂ),
      (∀ i v j, IsCharLabel (ι i v) (tameChar emb χ v.1.1 (e i v) j) (lab i v j)) ∧
      (∀ i, IsGood r (gp i) (s i) (lab i)) ∧
      (∀ i v, IsTypeChar (ι i v) (s i v) (loc i v)) ∧
      ∀ t, ch t = ∏ i, ∏ v : PlacesOver pb i,
        loc i v (Matrix.GeneralLinearGroup.map (e i v : kP v.1.1 →+* ZMod (gp i)) (t v.1))}

end Global

def GoodCharsGoodFamily : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (gp : Fin 2 → ℕ) [∀ i, Fact (gp i).Prime]
    (pb : Fin 2 → 𝓞 E), IsTypeDatum gp pb → ∀ (r m : ℕ)
    (e : ∀ i, ∀ v : PlacesOver pb i, kP v.1.1 ≃+* ZMod (gp i))
    (ι : ∀ i, PlacesOver pb i → ((Fbar (gp i))ˣ →* ℂˣ)), (∀ i v, Function.Injective (ι i v)) →
    ∀ (K : Type) [Field K] [NumberField K] (emb : K →+* ℂ),
    (∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (G0 (typePlaces pb) r))) →
    ∀ χ : ℕ → ∀ w : Pl E, (kP w)ˣ →* Kˣ,
    ∃ Xg : Finset (G0 (typePlaces pb) r → K),
      (∀ ch, ch ∈ goodChars gp pb r m e ι emb χ ↔ ∃ c ∈ Xg, ∀ t, ch t = emb (c t)) ∧
      (∀ c ∈ Xg, IsAbsIrrChar c) ∧
      ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 (typePlaces pb) r),
        ∀ c, c ∈ Xg ↔ ∃ s : T.S, ∀ t, c t = LinearMap.trace K (T.W s) (T.tau s t)

end GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues
