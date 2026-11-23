import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AbEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TriangularRepresentationDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResiduallyDiagonalRepresentation
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MaximalIdealImageKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimQuotientBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocalDeformationTraceModMaximal

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem localization_prime_generation {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ} (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3)
    (S : Space O F n) (x : Ideal S.A) (L : S.Loc x) {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ)
    (hh : h ≠ 0) (hs : ∀ a, F.Ψ (s a) = 1)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) →
      ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧
        ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1))
    (P : Ideal L.R) (hP : P.IsPrime) (h0 : L.ρ.triM ≤ P) (h1 : (maximalIdeal O).map (algebraMap O L.R) ≤ P)
    (h2 : ∀ a (i : Fin n), (i : ℕ) = 0 → L.ρ.r (s a) i i - 1 ∈ P)
    (h3 : ∀ a (i : Fin n), w n i = 0 → L.ρ.r (s' a) i i - 1 ∈ P) : S.mB.map L.b ≤ P := by
  haveI : IsLocalRing (L.R ⧸ P) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨hfin, hloc, hc, f, hf, hb⟩ := (local_deformation_trace_mod_maximal hF hn S x L).2.2 P h1
  have ht : (L.ρ.map (Ideal.Quotient.mk P)).triM = ⊥ := by
    rw [NRep.triM, Ideal.span_eq_bot]
    rintro _ ⟨g, i, j, hij, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h0 (Ideal.subset_span ⟨g, i, j, hij, rfl⟩))
  have hd := triangular_representation_diagonal hF hn f (L.ρ.map (Ideal.Quotient.mk P)) hc hb ht s s' h hh hs H
    (fun a i hi => Ideal.Quotient.eq.2 (h2 a i hi)) (fun a i hi => Ideal.Quotient.eq.2 (h3 a i hi))
  have hch : ∀ v g, ((L.ρ.map (Ideal.Quotient.mk P)).r (F.loc0 v g)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((L.ρ.map (Ideal.Quotient.mk P)).ψ v i g : L.R ⧸ P)) := fun v g => by
    have e := congrArg (Polynomial.map ((Ideal.Quotient.mk P).comp (L.ι : S.A →+* L.R))) (o1 hF hn S v g)
    rw [← Matrix.charpoly_map, Polynomial.map_prod] at e
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    exact e
  have hB := residually_diagonal_representation f _ hb ht hch hd
  have hm : ∀ y ∈ S.mB, L.b y ∈ maximalIdeal L.R := fun y hy => by
    have := (loc_flat hF hn S x L).2.2 hy
    rw [← L.lies] at this
    exact this
  have := maximal_ideal_image_kills hF hn S f ((Ideal.Quotient.mk P).comp (L.ι : S.A →+* L.R))
    (fun a => by rw [← hf]; exact congrArg (Ideal.Quotient.mk P) (L.ι.commutes a))
    (fun y hy => hloc _ (hm y hy)) ht hB
  exact Ideal.map_le_iff_le_comap.2 fun y hy =>
    Ideal.mem_comap.2 ((Ideal.Quotient.eq_zero_iff_mem (I := P)).1 (this y hy))

theorem UpperTheory.V.Fr.l51 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ L.ρ.triM) ≤ ((n - 1) * F.d + 2 + (3 * C₀ + 5) : ℕ) ∧ L.ρ.triP = ⊤ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hx
  refine ⟨?_, ((loc_rho hF hn S x L).2.2.2 hx).1⟩
  obtain ⟨s, s', h, hh, hs, hs', H⟩ := ab_gen hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ' := hϖ.maximalIdeal_eq
  obtain ⟨q1, q2, -⟩ := local_deformation_trace_mod_maximal hF hn S x L
  have hs1 : ∀ a, F.Ψ (s' a) = 1 := fun a => by
    obtain ⟨v, g, -, e, e'⟩ := hs' a
    rw [e']
    exact e
  let i0 : Fin n := ⟨0, by omega⟩
  let t : Unit ⊕ Fin (1 + C₀ + F.d) ⊕ ({i : Fin n // w n i = 0} × Fin F.d) → L.R :=
    Sum.elim (fun _ => algebraMap O L.R ϖ)
      (Sum.elim (fun a => L.ρ.r (s a) i0 i0 - 1) fun p => L.ρ.r (s' p.2) p.1 p.1 - 1)
  have hc := krull_dim_quotient_bound L.ρ.triM (S.mB.map L.b) t (by
      rintro (_ | a | p)
      · exact q1 (Ideal.mem_map_of_mem _ (hϖ' ▸ Ideal.mem_span_singleton_self ϖ))
      · exact q2 _ _ (hs a)
      · exact q2 _ _ (hs1 p.2))
    (fun P hP h0 ht => localization_prime_generation hF hn S x L s s' h hh hs H P hP h0
      (by rw [hϖ', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; exact ht (.inl ()))
      (fun a i hi => by
        obtain rfl : i = i0 := Fin.ext hi
        exact ht (.inr (.inl a)))
      (fun a i hi => ht (.inr (.inr (⟨i, hi⟩, a)))))
  have hw : Fintype.card {i : Fin n // w n i = 0} + 2 = n := by
    rcases hn with rfl | rfl <;> decide
  refine hc.trans ((add_le_add_left (fib_dim hF hn S x L hx) _).trans ?_)
  rw [← Nat.cast_add, Nat.cast_le]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  have e : n - 1 = Fintype.card {i : Fin n // w n i = 0} + 1 := by omega
  rw [e, add_mul]
  omega
