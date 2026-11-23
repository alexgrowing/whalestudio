import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.Tower

variable {R : Type} [CommRing R] {N : ℕ}

theorem sub_tail_mem (I : Ideal R) (e : ℕ) (G : ℕ → MvPolynomial (Fin (N + 1)) R)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) (m k : ℕ) :
    G m - G (m + k) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : G (m + k) - G (m + k + 1) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hd (m + k))
    have h3 : G m - G (m + (k + 1)) = (G m - G (m + k)) + (G (m + k) - G (m + k + 1)) := by
      rw [show m + (k + 1) = m + k + 1 from rfl]
      ring
    rw [h3]
    exact add_mem ih h2

theorem exists_limit_form (I : Ideal R) [IsPrecomplete I R] (n e : ℕ)
    (G : ℕ → MvPolynomial (Fin (N + 1)) R) (hom : ∀ i, (G i).IsHomogeneous n)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ g : MvPolynomial (Fin (N + 1)) R, g.IsHomogeneous n ∧
      ∀ i, G i - g ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have htop : ∀ k, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcoef : ∀ d i k, coeff d (G i) - coeff d (G (i + k)) ∈ I ^ (e + i + 1) := by
    intro d i k
    have h := (mem_map_C_iff.1 (sub_tail_mem I e G hd i k)) d
    rwa [coeff_sub] at h
  have hL : ∀ d, ∃ Ld : R, ∀ i, coeff d (G i) - Ld ∈ I ^ (e + i + 1) := by
    intro d
    obtain ⟨Ld, hLd⟩ := IsPrecomplete.prec' (I := I) (fun i => coeff d (G i)) (by
      intro m n hmn
      rw [SModEq.sub_mem, htop]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Ideal.pow_le_pow_right (by omega) (hcoef d m k))
    refine ⟨Ld, fun i => ?_⟩
    have h1 := hcoef d i (e + 1)
    have h2 := hLd (i + (e + 1))
    rw [SModEq.sub_mem, htop] at h2
    have h3 : coeff d (G i) - Ld =
        (coeff d (G i) - coeff d (G (i + (e + 1)))) + (coeff d (G (i + (e + 1))) - Ld) := by ring
    rw [h3]
    exact add_mem h1 (Ideal.pow_le_pow_right (by omega) h2)
  choose Lf hLf using hL
  refine ⟨∑ d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n, monomial d (Lf d), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun d hd => isHomogeneous_monomial _ ?_)
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [Finsupp.degree_eq_sum]
    exact hd.1
  · intro i
    rw [mem_map_C_iff]
    intro d
    rw [coeff_sub, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hdS : d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n
    · rw [if_pos hdS]
      exact hLf d i
    · rw [if_neg hdS, sub_zero]
      have h0 : coeff d (G i) = 0 := by
        by_contra hne
        apply hdS
        have hw := hom i hne
        rw [Finset.mem_finsuppAntidiag]
        refine ⟨?_, Finset.subset_univ _⟩
        rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
        exact hw
      rw [h0]
      exact zero_mem _

theorem exists_form_in_all (I : Ideal R) [IsPrecomplete I R]
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hanti : ∀ e, L (e + 1) ≤ L e) (n₀ : ℕ)
    (hlift : ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (e n : ℕ) (hn : n₀ ≤ n) (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ L e)
    (hgn : g.IsHomogeneous n) :
    ∃ g' : MvPolynomial (Fin (N + 1)) R, g'.IsHomogeneous n ∧ (∀ j, g' ∈ L j) ∧
      g - g' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have hL : Antitone L := antitone_nat_of_succ_le hanti
  let lift' : ℕ → MvPolynomial (Fin (N + 1)) R → MvPolynomial (Fin (N + 1)) R := fun j f =>
    if h : ∃ f' ∈ L (j + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (j + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) then h.choose else f
  let s : ℕ → MvPolynomial (Fin (N + 1)) R := fun i =>
    Nat.rec (motive := fun _ => MvPolynomial (Fin (N + 1)) R) g (fun k f => lift' (e + k) f) i
  have hsS : ∀ i, s (i + 1) = lift' (e + i) (s i) := fun i => rfl
  have hstep : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n →
      s (i + 1) ∈ L (e + i + 1) ∧ (s (i + 1)).IsHomogeneous n ∧
        s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    rintro i ⟨h1, h2⟩
    have hex := hlift (e + i) n hn (s i) h1 h2
    rw [hsS]
    simp only [lift']
    rw [dif_pos hex]
    exact hex.choose_spec
  have hinv : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n := by
    intro i
    induction i with
    | zero => exact ⟨hg, hgn⟩
    | succ i ih => exact ⟨(hstep i ih).1, (hstep i ih).2.1⟩
  have hd : ∀ i, s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
    fun i => (hstep i (hinv i)).2.2
  obtain ⟨g', hg'n, hg'⟩ := exists_limit_form I n e s (fun i => (hinv i).2) hd
  refine ⟨g', hg'n, fun j => ?_, hg' 0⟩
  have h1 : s j ∈ L j := hL (by omega : j ≤ e + j) (hinv j).1
  have h2 : s j - g' ∈ L j := hL (by omega : j ≤ e + j) (hbase (e + j) (hg' j))
  have h3 : g' = s j - (s j - g') := by ring
  rw [h3]
  exact sub_mem h1 h2

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_limit_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ I hI N L hhom hbase hanti n₀ hlift
  have : IsPrecomplete I R := hI.toIsPrecomplete
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) R) := {g | ∃ n, n₀ ≤ n ∧ g.IsHomogeneous n ∧ ∀ j, g ∈ L j}
  refine ⟨Ideal.span S, ?_, fun e => ⟨?_, ?_⟩⟩
  · intro d f hf
    have hH : (Ideal.span S).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) :=
      Ideal.homogeneous_span _ _ (fun x hx => by
        obtain ⟨n, _, hn, _⟩ := hx
        exact ⟨n, (mem_homogeneousSubmodule n x).2 hn⟩)
    have h := (Ideal.IsHomogeneous.mem_iff _ hH).1 hf d
    have e1 : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) f d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d f := decomposition.decompose'_apply f d
    rwa [e1] at h
  · rw [Ideal.span_le]
    rintro g ⟨n, _, _, hall⟩
    exact hall e
  · intro f hf k
    refine ⟨n₀, ?_⟩
    rw [← sum_homogeneousComponent f, Finset.mul_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hmem : X k ^ n₀ * homogeneousComponent d f ∈ L e := Ideal.mul_mem_left _ _ (hhom e d f hf)
    have hh : (X k ^ n₀ * homogeneousComponent d f).IsHomogeneous (n₀ + d) :=
      (isHomogeneous_X_pow k n₀).mul (homogeneousComponent_isHomogeneous d f)
    obtain ⟨g', hg'n, hall, hdiff⟩ :=
      exists_form_in_all I L hbase hanti n₀ hlift e (n₀ + d) (Nat.le_add_right _ _) _ hmem hh
    have h3 : X k ^ n₀ * homogeneousComponent d f = g' + (X k ^ n₀ * homogeneousComponent d f - g') := by
      ring
    rw [h3]
    exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨n₀ + d, Nat.le_add_right _ _, hg'n, hall⟩))
      (Ideal.mem_sup_right hdiff)

end GlobalTheory.CompanionTheory.GE.Tower
