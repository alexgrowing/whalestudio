import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPowEqOneLeOfIsCyclicUnits
open ReciprocityTheory.Gal

open Polynomial IntermediateField

namespace GlobalTheory.ShapeNeg

theorem natDegree_minpoly_le_mul {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) (hx : IsIntegral K x) :
    (minpoly ℚ_[p] x).natDegree ≤ (minpoly K x).natDegree * Module.finrank ℚ_[p] K := by
  set E := K⟮x⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hx
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  have h1 : Module.finrank ℚ_[p] K * Module.finrank K E = Module.finrank ℚ_[p] E :=
    Module.finrank_mul_finrank ℚ_[p] K E
  rw [adjoin.finrank hx] at h1
  have hxE : x ∈ E := mem_adjoin_simple_self K x
  haveI : IsScalarTower ℚ_[p] E (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h2 : minpoly ℚ_[p] (⟨x, hxE⟩ : E) = minpoly ℚ_[p] x :=
    (minpoly.algebraMap_eq (algebraMap E (PadicAlgCl p)).injective (⟨x, hxE⟩ : E)).symm
  have h3 := minpoly.natDegree_le (A := ℚ_[p]) (⟨x, hxE⟩ : E)
  rw [h2] at h3
  rw [mul_comm]
  omega

theorem natDegree_minpoly_le_card_pow_eq_one {p : ℕ} [Fact p.Prime]
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {N : ℕ} [NeZero N] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ) :
    (minpoly K ζ).natDegree ≤ Nat.card {x : ZMod N // x ^ k = 1} := by
  classical
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hirr : Irreducible (minpoly K ζ) := minpoly.irreducible hint
  have hsep : (minpoly K ζ).Separable := hirr.separable
  have hspl : Splits ((minpoly K ζ).map (algebraMap K (PadicAlgCl p))) := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl, ← Nat.card_eq_fintype_card]
  have hχ : ∀ σ : Formalism.GaloisCohomology.GK p K, ((hζ.autToPow K σ : ZMod N)) ^ k = 1 := by
    intro σ
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 := hζ.autToPow_spec K (σ ^ k)
    rw [hfix σ] at h1
    have h0 : ζ ^ (1 % N) = ζ := by rw [hζ.eq_orderOf, pow_mod_orderOf, pow_one]
    have h2 : ζ ^ (hζ.autToPow K (σ ^ k) : ZMod N).val = ζ ^ (1 % N) := h1.trans h0.symm
    have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
    rw [← ZMod.val_one_eq_one_mod] at h3
    exact ZMod.val_injective N h3
  have horb : ∀ y : (minpoly K ζ).rootSet (PadicAlgCl p), ∃ σ : Formalism.GaloisCohomology.GK p K, σ ζ = y := by
    intro y
    have hy : aeval (y : PadicAlgCl p) (minpoly K ζ) = 0 :=
      (mem_rootSet.1 y.2).2
    have he : minpoly K ζ = minpoly K (y : PadicAlgCl p) :=
      minpoly.eq_of_irreducible_of_monic hirr hy (minpoly.monic hint)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (PadicAlgCl p)).1 he.symm
    exact ⟨σ, hσ⟩
  choose σ hσ using horb
  refine Nat.card_le_card_of_injective (fun y => ⟨(hζ.autToPow K (σ y) : ZMod N), hχ (σ y)⟩) ?_
  intro y y' hyy
  have h : (hζ.autToPow K (σ y) : ZMod N) = (hζ.autToPow K (σ y') : ZMod N) :=
    congrArg Subtype.val hyy
  have h' : (σ y) ζ = (σ y') ζ := by
    rw [← hζ.autToPow_spec K (σ y), ← hζ.autToPow_spec K (σ y'), h]
  exact Subtype.ext (by rw [← hσ y, ← hσ y']; exact h')

theorem exists_pow_ne_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  intro p _ K hK k hk
  by_contra hcon
  push_neg at hcon
  have hp : p.Prime := Fact.out
  set d := Module.finrank ℚ_[p] K with hd
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * d < p ^ n := ⟨2 * k * d, Nat.lt_pow_self hp.one_lt⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  have hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ := fun σ => hcon σ (n + 1) ζ hζ.pow_eq_one
  have hB := natDegree_minpoly_le_card_pow_eq_one hζ k hfix
  have hC : Nat.card {x : ZMod (p ^ (n + 1)) // x ^ k = 1} ≤ 2 * k := by
    by_cases h2 : p = 2
    · subst h2
      exact GlobalTheory.card_pow_eq_one_two_pow_le (n + 1) (by omega) hk
    · haveI : IsCyclic (ZMod (p ^ (n + 1)))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 (n + 1)
      have := GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (p ^ (n + 1)) hk
      omega
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  have hA := natDegree_minpoly_le_mul hK ζ hint
  have hcyc : cyclotomic (p ^ (n + 1)) ℚ_[p] = minpoly ℚ_[p] ζ := by
    refine minpoly.eq_of_irreducible_of_monic (GlobalTheory.Cyc.Model.cyc_irred n) ?_ (cyclotomic.monic _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos _)
  rw [← hcyc, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hA
  rw [← hd] at hA
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h1 : p ^ n ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ hp1
  have h2 : (minpoly K ζ).natDegree * d ≤ 2 * k * d := Nat.mul_le_mul_right _ (hB.trans hC)
  omega

end GlobalTheory.ShapeNeg
