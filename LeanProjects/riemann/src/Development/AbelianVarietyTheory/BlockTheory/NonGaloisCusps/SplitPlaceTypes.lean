import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

section Host

variable {R : Ranks} (H : Host R)

def SplitRowPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l ∧ l ≠ H.q ∧ l ≠ H.d ∧ (∀ k, l ≠ H.g k) ∧ H.cls l = PrimeClass.splitK

def halfType (s : Bool) : Set (H.E →+* ℂ) :=
  match s with
  | true => H.cmType
  | false => {φ | φ.comp (H.conj : H.E →+* H.E) ∈ H.cmType}

def PlacesSplit (l : ℕ) : Prop :=
  ∀ w ∈ placesOver H.E l,
    w.asIdeal.ramificationIdx ℤ = 1 ∧
    (∃ w' ∈ placesOver H.E l, IsConjPl H w w') ∧
    ∀ w', IsConjPl H w w' → w' ≠ w

end Host

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
  (nbr : Br.NBr N) (i : N.Loc)

def EmbIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  (∀ x : H.E, ∃ y : what₂.LL, Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x)) ∧
  ∃ φ ∈ halfType H s,
    ∀ (x : H.E) (y : what₂.LL), Br.toLLK (nbr i w hw) (N.embK i y) = τ (Br.cEw nbr i w hw x) →
      what₂.embLL y = φ x

def PlIn (s : Bool) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) : Prop :=
  Nonempty (Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) ∧ ∀ τ, EmbIn nbr i s w hw τ

def columns (s : Bool) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | ∃ hw : w ∈ placesOver H.E (N.l i), PlIn nbr i s w hw}

def TypesPair : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)),
    Loc.K0 (nbr i w hw).Kw = (nbr i w hw).Kw.1) ∧
  (∀ (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)) τ,
    ¬ (EmbIn nbr i true w hw τ ∧ EmbIn nbr i false w hw τ)) ∧
  (∀ (w w' : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
      (hw' : w' ∈ placesOver H.E (N.l i)), IsConjPl H w w' →
    (PlIn nbr i true w hw ∧ PlIn nbr i false w' hw') ∨
      (PlIn nbr i false w hw ∧ PlIn nbr i true w' hw')) ∧
  ∀ s : Bool,
    (∀ w ∈ placesOver H.E (N.l i), ∀ w', IsConjPl H w w' →
      Xor' (w ∈ columns nbr i s) (w' ∈ columns nbr i s)) ∧
    (columns nbr i s).Finite ∧
    ∀ w ∈ placesOver H.E (N.l i), locDeg H.E w * (columns nbr i s).ncard = R.f

end Loc

def SplitRow_at (D : D7) : Prop :=
  (∀ l : ℕ, SplitRowPrime D.host l → PlacesSplit D.host l) ∧
  ∀ i : D.nd.Loc, SplitRowPrime D.host (D.nd.l i) → TypesPair (N := D.nd) D.nbr i

def SplitRowF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, SplitRow_at (Fm.D x i)

def SplitRowClosed (C : FamClass) : Prop := Closed C (fun Fm _ => SplitRowF Fm)

example {R : Ranks} (H : Host R) : ∃ l, SplitRowPrime H l := by
  have hd : H.d ≠ 0 := H.hyp.2.1.ne_zero
  obtain ⟨l, hl, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one
    (5 + H.q + H.d + H.g 0 + H.g 1 + H.small.sup id) (k := 4 * H.d) (by omega)
  have hs : l ∉ H.small := fun h => by
    have : l ≤ H.small.sup id := Finset.le_sup (f := id) h
    omega
  have hq : l ≠ H.q := by omega
  have hd' : l ≠ H.d := by omega
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hj : jacobiSym (-(H.d : ℤ)) l = 1 := by
    rw [jacobiSym.mod_right _ hodd]
    have h1 : l % (4 * (-(H.d : ℤ)).natAbs) = 1 := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      have h := hmod
      unfold Nat.ModEq at h
      rw [h]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, jacobiSym.one_right]
  refine ⟨l, hl, by omega, hq, hd', ?_, ?_⟩
  · intro k
    fin_cases k
    · show l ≠ H.g 0
      omega
    · show l ≠ H.g 1
      omega
  · unfold Host.cls primeClass
    rw [if_neg hs, if_neg hq, if_neg hd', if_pos hj]

end GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

end
