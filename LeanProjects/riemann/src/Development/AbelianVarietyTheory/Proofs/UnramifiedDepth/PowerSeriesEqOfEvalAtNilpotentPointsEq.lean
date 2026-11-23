import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def lowZero {A κ : Type} [CommRing A] (e : κ →₀ ℕ) : Ideal (MvPowerSeries κ A) where
  carrier := {g | ∀ e' ≤ e, MvPowerSeries.coeff e' g = 0}
  add_mem' {a b} ha hb e' h := by rw [map_add, ha e' h, hb e' h, add_zero]
  zero_mem' e' _ := map_zero _
  smul_mem' c x hx e' h := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2 (le_trans (le_of_le_of_eq le_add_self (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)) h), mul_zero]

private theorem coeff_box {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (N : ℕ) (c : (κ →₀ ℕ) → A)
    (e : κ →₀ ℕ) (he : ∀ i, e i < N) :
    MvPowerSeries.coeff e (∑ b : κ → Fin N, MvPowerSeries.C (c (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
      ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ (b i : ℕ)) = c e := by
  have hm : ∀ b : κ → ℕ, ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ b i =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm b) 1 := fun b => by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have he' : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, he i⟩ : Fin N) : ℕ)) = e := by
    ext i; rfl
  rw [map_sum, Finset.sum_eq_single (fun i => (⟨e i, he i⟩ : Fin N))]
  · rw [hm, MvPowerSeries.coeff_C_mul, he', MvPowerSeries.coeff_monomial_same, _root_.mul_one]
  · intro b _ hb
    rw [hm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial_ne, mul_zero]
    intro h
    exact hb (funext fun i => Fin.ext (by simp [h]))
  · simp

theorem eq_of_nv_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  intro R _ I hI n d f f' H
  ext e
  rw [← sub_eq_zero]
  refine hI.haus _ fun k => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  let A := R ⧸ I ^ (k + 1)
  let J : Ideal (MvPowerSeries (Fin n × Fin d) A) := lowZero e
  let N : ℕ := (∑ i, e i) + 1
  have he : ∀ i, e i < N := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have halg : ∀ t : R, algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J) t =
      Ideal.Quotient.mk J (MvPowerSeries.C (Ideal.Quotient.mk (I ^ (k + 1)) t)) := fun t => by
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]; rfl
  have hN : ∀ q : Fin n × Fin d, (Ideal.Quotient.mk J (MvPowerSeries.X q)) ^ N = 0 := fun q => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    intro e' h
    exact (MvPowerSeries.X_pow_dvd_iff.1 dvd_rfl) e' (lt_of_le_of_lt (h q) (he q))
  have hv : ∀ g : PS R n d, nv (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)) g
      (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) =
      Ideal.Quotient.mk J (∑ b : Fin n × Fin d → Fin N, MvPowerSeries.C ((fun x => Ideal.Quotient.mk (I ^ (k + 1))
        (MvPowerSeries.coeff x g)) (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
        ∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n × Fin d) A) ^ (b i : ℕ)) := fun g => by
    letI := (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)).toAlgebra
    refine (evBasic_nEval_eq_tEval g (fun q : Fin n × Fin d => Ideal.Quotient.mk J (MvPowerSeries.X q)) N hN).trans ?_
    simp only [tEval, map_sum, map_mul, map_prod, map_pow]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (halg _)
  have h := H (MvPowerSeries (Fin n × Fin d) A ⧸ J) k (fun t ht => by
      rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero, map_zero]) (fun hR hne => ?_)
    (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) (fun i j => ⟨N, hN (i, j)⟩)
  · rw [hv, hv, Ideal.Quotient.eq] at h
    have h2 := h e le_rfl
    rw [map_sub, sub_eq_zero] at h2
    exact Ideal.Quotient.eq.1 (((coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f)) e he).symm.trans h2).trans (coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f')) e he))
  · have hA : I ^ (k + 1) ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero k)))
    haveI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hA
    haveI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hJ : J ≠ ⊤ := fun h => by
      have : (1 : MvPowerSeries (Fin n × Fin d) A) ∈ J := h ▸ Submodule.mem_top
      have := this 0 zero_le
      simp at this
    haveI : Nontrivial (MvPowerSeries (Fin n × Fin d) A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
    refine ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ⟨fun t ht => ?_⟩⟩
    rw [halg] at ht
    have h1 := (IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).map_nonunit _ ht
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h1
    exact (IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (k + 1))) Ideal.Quotient.mk_surjective).map_nonunit _ h1

end GlobalTheory.ChF
