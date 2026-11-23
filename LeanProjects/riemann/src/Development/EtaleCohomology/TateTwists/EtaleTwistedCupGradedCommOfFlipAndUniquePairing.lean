import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTwistedCupProductGradedCommutative

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a

def LateralTheory.EtaleFoundations.cc_flip_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν

def LateralTheory.EtaleFoundations.cc_twpair : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair (htw : LateralTheory.EtaleFoundations.cc_twpair) (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
    (a : Ht q E n i) (b : Ht q E m j) (k : ℤ) (hk : j + i = k)
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hν : IsTwPair ν) (w : ℤ) (hw : m + n = w) :
    ν.cup E hw b a = (cup q b a).cast hw hk := by
  subst hk hw
  obtain ⟨h1, h2⟩ := htw q j i
  have := h2 (j + i) rfl ν (twPair q j i) hν h1 E (n := m) (m := n) rfl
  rw [this]
  rfl

theorem LateralTheory.EtaleFoundations.etale_twisted_cup_graded_comm_of_flip_and_unique_pairing (hflip : LateralTheory.EtaleFoundations.cc_cup_flip) (hex : LateralTheory.EtaleFoundations.cc_flip_ex)
    (htw : LateralTheory.EtaleFoundations.cc_twpair) : LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative := by
  intro q _ E n m i j a b
  obtain ⟨ν, hν⟩ := hex (ZMod q) (twPair q i j)
  have hνtw : IsTwPair ν := by
    intro U ζ
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [this, (htw q i j).1 U ζ]
    simp
  have e1 : cup q a b = (n * m).negOnePow • ν.cup E (add_comm m n) b a :=
    hflip (ZMod q) (twPair q i j) ν hν E rfl (add_comm m n) a b
  rw [e1, LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair htw q E a b (i + j) (add_comm j i) ν hνtw (n + m) (add_comm m n)]
