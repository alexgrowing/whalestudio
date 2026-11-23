import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.HensNewton
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.PlNormal
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem eig_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : O) (hF : F ≠ 0) :
    ∃ K : ℕ, ∀ b : O, b - F ∈ maximalIdeal O ^ K → b ∣ F := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hF hp
  refine ⟨v + 1, fun b hb => ?_⟩
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  have hun : IsUnit ((u : O) + p * c) := by
    by_contra hn
    have h1 : (u : O) + p * c ∈ maximalIdeal O := hn
    have h2 : p * c ∈ maximalIdeal O := Ideal.mul_mem_right _ _ hp.not_isUnit
    have h3 : (u : O) ∈ maximalIdeal O := by simpa using Ideal.sub_mem _ h1 h2
    exact h3 u.isUnit
  have hb' : b = ((u : O) + p * c) * p ^ v := by
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, hu]; ring
  rw [hb', hu, hun.mul_left_dvd]
  exact Dvd.intro_left _ rfl

private theorem eig_fEl {O : Type} [CommRing O] (I : Ideal O) {q n : ℕ} (Nq : Fin q → ℕ)
    (hN : ∀ j, (Nq j : O) - 1 ∈ I) (a b : Fin q → Fin n → O) (h : ∀ j i, a j i - b j i ∈ I) :
    fEl Nq a - fEl (fun _ => 1) b ∈ I := by
  rw [← Ideal.Quotient.eq]
  have h1 : ∀ j, Ideal.Quotient.mk I (Nq j : O) = 1 := fun j => by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hN j
  have h2 : ∀ j i, Ideal.Quotient.mk I (a j i) = Ideal.Quotient.mk I (b j i) := fun j i =>
    Ideal.Quotient.eq.2 (h j i)
  simp only [fEl, map_prod, map_mul, map_sub, h1, h2, Nat.cast_one, map_one]

private theorem eig_chp {O : Type} [CommRing O] (I : Ideal O) {n : ℕ} (A B : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, A a b - B a b ∈ I) (k : ℕ) : A.charpoly.coeff k - B.charpoly.coeff k ∈ I := by
  rw [← Ideal.Quotient.eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map,
    ← Matrix.charpoly_map]
  congr 2
  ext a b
  exact Ideal.Quotient.eq.2 (h a b)

theorem UpperTheory.V.Th.Sp.eig :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → Th.Eig y T al → ∃ F : O, F ≠ 0 ∧ ∀ᶠ N in atTop, ∃ α : Fin T.q → Fin n → O, (∀ j, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α j i))) ∧ fEl (T.Nq N) α ∣ F := by
  intro l _ L G0 T n O _ _ _ hc _ y al hP hE
  haveI : IsAdicComplete (maximalIdeal O) O := hc.complete
  have hF : fEl (fun _ => 1) al ≠ 0 := by
    simp only [fEl, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have hne : al j i - al j i' ≠ 0 := fun h0 =>
      (Finset.ne_of_mem_erase hi') ((hE j).1 (sub_eq_zero.1 h0)).symm
    exact mul_ne_zero hne hne
  obtain ⟨K, hK⟩ := eig_dvd _ hF
  refine ⟨_, hF, ?_⟩
  choose K' hK' using fun j => UpperTheory.V.Th.Sp.hens O n (al j) (hE j).1 K
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := hc.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  filter_upwards [UpperTheory.V.Th.Sp.close l L G0 T n O y hP (Finset.univ.sup K'), eventually_ge_atTop K] with N hN hNK
  have key : ∀ j, ∃ α : Fin n → O, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (α i)) ∧ ∀ i, α i - al j i ∈ maximalIdeal O ^ K := by
    intro j
    refine hK' j _ (Matrix.charpoly_monic _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) fun k => ?_
    rw [← (hE j).2]
    exact Ideal.pow_le_pow_right (Finset.le_sup (f := K') (Finset.mem_univ j)) (eig_chp _ _ _ (hN j) k)
  choose α h1 h2 using key
  refine ⟨α, h1, hK _ (eig_fEl _ _ (fun j => ?_) _ _ h2)⟩
  obtain ⟨c, hc'⟩ := (T.Nq_mod N j).symm.dvd
  have h3 : (T.Nq N j : O) - 1 = (l : O) ^ N * (c : O) := by
    have := congrArg (Int.cast : ℤ → O) hc'
    simpa using this
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hNK (Ideal.pow_mem_pow hlO N))
