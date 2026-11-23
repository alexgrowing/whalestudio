import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.RootPolyFactor

open GlobalTheory.GoodCharsCompare

theorem card_sigma_cyc {r : ℕ} (b : Fin r → Fin r) :
    Fintype.card (Σ c : Cyc b, Fin (cycLen b c)) = r := by
  have e : (Σ c : Cyc b, {i : Fin r // b i = c.1}) ≃ Fin r :=
    { toFun := fun y => y.2.1
      invFun := fun i => ⟨⟨b i, i, rfl⟩, i, rfl⟩
      left_inv := by
        rintro ⟨⟨c, hc⟩, i, hi⟩
        cases hi
        rfl
      right_inv := fun i => rfl }
  have := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at this
  rw [Fintype.card_sigma]
  simpa using this

theorem rootsBar_prod {p : ℕ} [Fact p.Prime] {ι : Type} (s : Finset ι) (φ : ι → (ZMod p)[X])
    (h : ∀ c, (φ c).Monic) {z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (∏ c ∈ s, φ c) ↔ ∃ c ∈ s, z ∈ Formalism.CyclotomicNorms.rootsBar (φ c) := by
  rw [mem_rootsBar (monic_prod_of_monic _ _ fun c _ => h c).ne_zero, map_prod, Finset.prod_eq_zero_iff]
  simp only [mem_rootsBar (h _).ne_zero]

theorem dg_eq {p : ℕ} [Fact p.Prime] {r : ℕ} {b : Fin r → Fin r} {x : Cyc b → Fbar p}
    (hx : ∀ c, x c ^ (p ^ cycLen b c - 1) = 1) (hinj : Function.Injective (rootElt x)) (c : Cyc b) :
    dg (x c) = cycLen b c := by
  obtain ⟨k, hk⟩ := exists_dg_mul (cycLen_pos b c) (hx c)
  have h0 := cycLen_pos b c
  have hle : dg (x c) ≤ cycLen b c := Nat.le_of_dvd h0 ⟨k, hk⟩
  by_contra hne
  have hlt : dg (x c) < cycLen b c := lt_of_le_of_ne hle hne
  have := @hinj ⟨c, ⟨dg (x c), hlt⟩⟩ ⟨c, ⟨0, h0⟩⟩ (by
    show x c ^ p ^ dg (x c) = x c ^ p ^ 0
    rw [(frobenius_orbit_degreeOverPrimeFieldFbar (x c)).1, pow_zero, pow_one])
  have h2 := congrArg (fun y : (Σ c : Cyc b, Fin (cycLen b c)) => (y.2 : ℕ)) this
  exact (dg_pos (x c)).ne' h2

theorem mem_roots_lt {p : ℕ} [Fact p.Prime] {y z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) ↔ ∃ i < dg y, y ^ p ^ i = z := by
  classical
  rw [← Multiset.mem_toFinset, roots_minpoly]
  simp

theorem rootPoly_factor : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  intro p _ r b x f ⟨hx, hm, hr⟩
  have hdeg : f.natDegree = r := by
    rw [← card_rootsBar, hr, Multiset.card_map, ← Finset.card_def, Finset.card_univ, card_sigma_cyc]
  have hsq : Squarefree f ↔ Function.Injective (rootElt x) := by
    rw [squarefree_iff hm.ne_zero, hr, Multiset.nodup_map_iff_inj_on Finset.univ.nodup]
    simp [Function.Injective]
  refine ⟨hdeg, ?_, hsq, fun hs => ?_⟩
  · rw [coeff_zero_iff hm.ne_zero, hr, Multiset.mem_map]
    rintro ⟨⟨c, i⟩, -, h⟩
    have h1 : x c = 0 := eq_zero_of_pow_eq_zero h
    have := hx c
    rw [h1, zero_pow (g_pow_sub_pos (cycLen_pos b c)).ne'] at this
    exact zero_ne_one this
  · have hinj := hsq.1 hs
    have hd := dg_eq hx hinj
    refine ⟨hd, fun c c' h => ?_, ?_⟩
    · have h1 : x c' ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (x c)) := by
        rw [show minpoly (ZMod p) (x c) = minpoly (ZMod p) (x c') from h]
        exact mem_roots_minpoly.2 ⟨0, by simp⟩
      obtain ⟨i, hi, e⟩ := mem_roots_lt.1 h1
      have := @hinj ⟨c, ⟨i, hd c ▸ hi⟩⟩ ⟨c', ⟨0, cycLen_pos b c'⟩⟩ (by
        show x c ^ p ^ i = x c' ^ p ^ 0
        rw [e, pow_zero, pow_one])
      exact congrArg Sigma.fst this
    · have hmon : ∀ c, (minpoly (ZMod p) (x c)).Monic := fun c => minpoly.monic (isInt _)
      have hP := monic_prod_of_monic Finset.univ _ fun c _ => hmon c
      apply eq_of_rootsBar hm hP
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset ((squarefree_iff hm.ne_zero).1 hs)]
        intro z hz
        rw [hr, Multiset.mem_map] at hz
        obtain ⟨⟨c, i⟩, -, rfl⟩ := hz
        exact (rootsBar_prod _ _ hmon).2 ⟨c, Finset.mem_univ _, mem_roots_minpoly.2 ⟨i, rfl⟩⟩
      · rw [card_rootsBar, card_rootsBar, hdeg, natDegree_prod_of_monic _ _ fun c _ => hmon c]
        have := card_sigma_cyc b
        rw [Fintype.card_sigma] at this
        simp only [Fintype.card_fin] at this
        exact ((Finset.sum_congr rfl fun c _ => hd c).trans this).le

end GlobalTheory.ParamLabel.RootPolyFactor
