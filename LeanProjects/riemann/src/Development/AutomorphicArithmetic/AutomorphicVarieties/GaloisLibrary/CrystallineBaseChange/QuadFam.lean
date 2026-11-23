import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
import Mathlib.NumberTheory.LSeries.PrimesInAP

open NumberField

private theorem quadFam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) := by
  obtain ⟨K, hF, hN, hr, hd⟩ := KStar.Consta.exists_quadField hp h4
  have hp0 : p ≠ 0 := hp.ne_zero
  have htc : IsTotallyComplex K :=
    (KStar.Choice.exists_sq_eq_neg_of_discr hr hp0 hd).2
  have hq : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hr }
  exact ⟨K, hF, hN, IsCMField.ofCMExtension ℚ K, hr, hd⟩

theorem UpperTheory.V.Br.quadFam :
    UpperTheory.V.Br.QuadFam := by
  intro N
  have hS : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨p, hpn, hpp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 3) (by norm_num) (by norm_num)
    exact ⟨p, ⟨hpp, hmod⟩, hpn⟩
  let e := hS.natEmbedding
  let q : Fin N → ℕ := fun i => (e i.val).1
  have hq : ∀ i, (q i).Prime ∧ q i % 4 = 3 := fun i => (e i.val).2
  have hinj : ∀ i j, q i = q j → i = j := fun i j h =>
    Fin.ext (e.injective (Subtype.ext h))
  choose K hF hN hC hr hd using fun i => quadFam_one (q i) (hq i).1 (hq i).2
  refine ⟨K, hF, hN, hC, hr, ?_⟩
  intro i j hij
  rw [hd i, hd j]
  have hne : q i ≠ q j := fun h => hij (hinj i j h)
  have hcop : Nat.Coprime (q i) (q j) := (Nat.coprime_primes (hq i).1 (hq j).1).2 hne
  exact (Nat.isCoprime_iff_coprime.2 hcop).neg_neg
