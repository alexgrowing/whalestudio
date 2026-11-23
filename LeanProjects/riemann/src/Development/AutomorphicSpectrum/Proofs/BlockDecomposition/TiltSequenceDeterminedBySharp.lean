import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem tilt_inj {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A)
    (ha : ∀ i, a (i + 1) ^ l = a i) (hb : ∀ i, b (i + 1) ^ l = b i)
    (hs : ∀ i, A.sharp (a i) = A.sharp (b i)) : a = b := by
  have hf : ∀ x y : A.A, (x - y) ^ l = x ^ l - y ^ l := fun x y => map_sub A.frob x y
  have key : ∀ j i, a i - b i = (a (i + j) - b (i + j)) ^ (l ^ j) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      rw [ih i, pow_succ' l j, pow_mul, hf, ← add_assoc, ha, hb]
  have hmem : ∀ j, a j - b j ∈ Ideal.span {A.pi} := by
    intro j
    rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, A.sharpMap_eq, A.sharpMap_eq,
      hs j, sub_self]
  have hdvd : ∀ i j, A.pi ^ j ∣ a i - b i := by
    intro i j
    have h1 : A.pi ∣ a (i + j) - b (i + j) := Ideal.mem_span_singleton.1 (hmem (i + j))
    rw [key j i]
    exact (pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)
  have hH : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  funext i
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (hdvd i n)

end GlobalTheory.CompanionTheory.Untilt
