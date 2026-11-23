import Mathlib

noncomputable section

namespace SheetDecomposition.CovAlg

open Polynomial

def mon {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := X ^ d + ∑ j, C (a j) * X ^ (j : ℕ)

def low {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : R[X] := ∑ j, C (a j) * X ^ (j : ℕ)

theorem mon_map {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) :
    (mon a).map f = mon fun j => f (a j) := by
  simp [mon, Polynomial.map_sum]

theorem eval₂_low {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (a : Fin d → R) (f : R →+* S) (x : S) :
    eval₂ f x (low a) = ∑ j, f (a j) * x ^ (j : ℕ) := by
  simp [low, eval₂_finset_sum]

theorem mon_monic {R : Type} [CommRing R] {d : ℕ} (a : Fin d → R) : (mon a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

theorem exists_prim (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] [Algebra Ω₀ Ω] (d : ℕ) (hd : 0 < d)
    (hfin : Module.finrank Ω₀ Ω = d) {σ : Type} [Fintype σ] (t : σ → Ω)
    (ht : Algebra.adjoin Ω₀ (Set.range t) = ⊤) (γ : Ω) :
    ∃ (θ : Ω) (T : Set Ω₀), T.Finite ∧ ∀ (R : Type) [CommRing R] (i : R →+* Ω₀), Function.Injective i →
      T ⊆ Set.range i → ∃ (a : Fin d → R) (cf : σ → Fin d → R) (G : R[X]) (Q : MvPolynomial σ R),
        (mon a).Separable ∧ (∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) θ F = 0 ↔ mon a ∣ F) ∧
        (∀ s, eval₂ ((algebraMap Ω₀ Ω).comp i) θ (low (cf s)) = t s) ∧
        eval₂ ((algebraMap Ω₀ Ω).comp i) θ G = γ ∧ MvPolynomial.eval₂ ((algebraMap Ω₀ Ω).comp i) t Q = θ := by
  classical
  haveI : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  haveI : CharZero Ω₀ := (algebraMap Ω₀ Ω).charZero
  let pb := Field.powerBasisOfFiniteOfSeparable Ω₀ Ω
  obtain rfl : pb.dim = d := pb.finrank.symm.trans hfin
  have hint : IsIntegral Ω₀ pb.gen := pb.isIntegral_gen
  let a₀ : Fin pb.dim → Ω₀ := fun j => (minpoly Ω₀ pb.gen).coeff j
  have hP : mon a₀ = minpoly Ω₀ pb.gen := by
    conv_rhs => rw [(minpoly.monic hint).as_sum, pb.natDegree_minpoly, Finset.sum_range]
    rfl
  let cf₀ : σ → Fin pb.dim → Ω₀ := fun s j => pb.basis.repr (t s) j
  have hcf : ∀ s, ∑ j, algebraMap Ω₀ Ω (cf₀ s j) * pb.gen ^ (j : ℕ) = t s := fun s => by
    conv_rhs => rw [← pb.basis.sum_repr (t s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pb.basis_eq_pow, Algebra.smul_def]
  obtain ⟨G₀, hG₀⟩ := pb.exists_eq_aeval' γ
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : MvPolynomial σ Ω₀, MvPolynomial.aeval t Q₀ = pb.gen := by
    have : pb.gen ∈ Algebra.adjoin Ω₀ (Set.range t) := ht ▸ Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  obtain ⟨u₀, v₀, huv⟩ : (minpoly Ω₀ pb.gen).Separable := Algebra.IsSeparable.isSeparable Ω₀ pb.gen
  refine ⟨pb.gen, Set.range a₀ ∪ Set.range (fun q : σ × Fin pb.dim => cf₀ q.1 q.2) ∪ G₀.coeffs ∪ Q₀.coeffs ∪
    u₀.coeffs ∪ v₀.coeffs, by
      simp only [Set.finite_union, Set.finite_range, Finset.finite_toSet, and_self], ?_⟩
  intro R _ i hi hT
  simp only [Set.union_subset_iff] at hT
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hT
  choose a ha using fun j => h1 ⟨j, rfl⟩
  choose cf hcf' using fun s j => h2 ⟨(s, j), rfl⟩
  obtain ⟨G, hG⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h3)
  obtain ⟨u, hu⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h5)
  obtain ⟨v, hv⟩ := (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 h6)
  obtain ⟨Q, hQ⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.2 h4
  have hm : (mon a).map i = minpoly Ω₀ pb.gen := by
    rw [mon_map, ← hP]
    exact congrArg mon (funext ha)
  have hev : ∀ F : R[X], eval₂ ((algebraMap Ω₀ Ω).comp i) pb.gen F = aeval pb.gen (F.map i) := fun F => by
    rw [aeval_def, eval₂_map]
  refine ⟨a, cf, G, Q, ⟨u, v, ?_⟩, fun F => ?_, fun s => ?_, ?_, ?_⟩
  · apply map_injective i hi
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hm, hu, hv, huv,
      Polynomial.map_one]
  · rw [hev, ← map_dvd_map i hi (mon_monic a), hm, minpoly.dvd_iff]
  · rw [eval₂_low, ← hcf s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.comp_apply, hcf']
  · rw [hev, hG, hG₀]
  · rw [← MvPolynomial.eval₂_map, hQ, ← hQ₀, MvPolynomial.aeval_def]

end SheetDecomposition.CovAlg
