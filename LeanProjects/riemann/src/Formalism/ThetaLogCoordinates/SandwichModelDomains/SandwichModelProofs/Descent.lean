import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem dsc_denominator (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g ∈ dualWeyl ℤ r n ν, N • g ∈ weyl ℤ r n hn ν := by
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r n ν
  have : Fintype (ssIdx r n ν) := (sSIdxFinite r n ν).fintype
  have hb : ∀ i, b i ∈ dualWeyl ℤ r n ν := fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc0 hc using fun i => weylRational r n hn ν hν (b i) (hb i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i, fun g hg => ?_⟩
  rw [← hspan] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i), mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hc i)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dsc_split (p : ℕ) [hp : Fact p.Prime] (N : ℤ) (hN : N ≠ 0) :
    ∃ (k : ℕ) (c : ℤ), N = (p : ℤ) ^ k * c ∧ ¬ (p : ℤ) ∣ c := by
  have hfin : FiniteMultiplicity (p : ℤ) N :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.out.ne_one, hN⟩
  obtain ⟨c, h1, h2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, h1, h2⟩

theorem dsc_approx (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (k : ℕ)
    (y : MvPolynomial (Fin r × Fin n) ℤ_[p]) (hy : y ∈ weyl ℤ_[p] r n hn ν) :
    ∃ d ∈ weyl ℤ r n hn ν, ∃ z : MvPolynomial (Fin r × Fin n) ℤ_[p],
      y = map (Int.castRingHom ℤ_[p]) d + ((p : ℤ_[p]) ^ k) • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, 0, ?_⟩
    simp only [smul_zero, add_zero]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, z1, rfl⟩ := hx
    obtain ⟨d2, hd2, z2, rfl⟩ := hy
    refine ⟨d1 + d2, Submodule.add_mem _ hd1 hd2, z1 + z2, ?_⟩
    rw [map_add, smul_add]; abel
  | smul a x _ hx =>
    obtain ⟨d, hd, z, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ k * a' := by
      rw [← ha']; ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • d, Submodule.smul_mem _ _ hd,
      a' • map (Int.castRingHom ℤ_[p]) d + a • z, ?_⟩
    have hm : map (Int.castRingHom ℤ_[p]) (((PadicInt.appr a k : ℕ) : ℤ) • d) =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]; simp
    have h1 : a • map (Int.castRingHom ℤ_[p]) d =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d +
          ((p : ℤ_[p]) ^ k * a') • map (Int.castRingHom ℤ_[p]) d := by
      rw [← add_smul, ← ha]
    rw [hm, smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a, h1, add_assoc]

theorem dsc_divide (p : ℕ) [Fact p.Prime] {σ : Type*} (k : ℕ) (g : MvPolynomial σ ℤ)
    (z : MvPolynomial σ ℤ_[p]) (h : map (Int.castRingHom ℤ_[p]) g = ((p : ℤ_[p]) ^ k) • z) :
    ∃ g1 : MvPolynomial σ ℤ, g = ((p : ℤ) ^ k) • g1 := by
  have hd : C ((p : ℤ) ^ k) ∣ g := by
    rw [C_dvd_iff_dvd_coeff]
    intro m
    rw [← PadicInt.pow_p_dvd_int_iff]
    have := congrArg (coeff m) h
    rw [coeff_map, coeff_smul] at this
    exact ⟨coeff m z, by simpa using this⟩
  obtain ⟨g1, rfl⟩ := hd
  exact ⟨g1, by rw [smul_eq_C_mul]⟩

theorem descent_over_integers : DescentZ := by
  intro p _ r n hn ν hν e hyp f hf
  obtain ⟨N, hN0, hN⟩ := dsc_denominator r n hn ν hν
  obtain ⟨k, c, hNc, hc⟩ := dsc_split p N hN0
  have hmf : map (Int.castRingHom ℤ_[p]) f ∈ dualWeyl ℤ_[p] r n ν :=
    dualWeylMap ℤ ℤ_[p] (Int.castRingHom ℤ_[p]) r n ν f hf
  obtain ⟨d, hd, z, hz⟩ := dsc_approx p r n hn ν k _ (hyp _ hmf)
  have hmap : map (Int.castRingHom ℤ_[p]) (((p : ℤ) ^ e) • f - d) = ((p : ℤ_[p]) ^ k) • z := by
    rw [map_sub, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    have : (Int.castRingHom ℤ_[p]) ((p : ℤ) ^ e) = (p : ℤ_[p]) ^ e := by simp
    rw [this, hz]; abel
  obtain ⟨g1, hg1⟩ := dsc_divide p k _ z hmap
  have hg0 : ((p : ℤ) ^ e) • f - d ∈ dualWeyl ℤ r n ν :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (weylLeDual ℤ r n hn ν hν hd)
  have hpk : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hg1m : g1 ∈ dualWeyl ℤ r n ν := dualWeylSat ℤ r n ν _ g1 hpk (hg1 ▸ hg0)
  refine ⟨c, hc, ?_⟩
  have key : (c * (p : ℤ) ^ e) • f = c • d + N • g1 := by
    rw [hNc, mul_comm ((p : ℤ) ^ k) c, mul_smul, mul_smul, ← hg1, smul_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hd) (hN g1 hg1m)

end Formalism.InvariantFactorPaths.INST
