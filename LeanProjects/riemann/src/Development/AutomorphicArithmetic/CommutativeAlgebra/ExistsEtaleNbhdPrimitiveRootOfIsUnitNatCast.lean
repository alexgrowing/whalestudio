import Mathlib
import Development.EtaleCohomology.EtaleSheaves.DerivUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

private theorem evalRoot {A : Type} [CommRing A] (q : ℕ) :
    Polynomial.eval (AdjoinRoot.root (Polynomial.cyclotomic q A))
      (Polynomial.cyclotomic q (AdjoinRoot (Polynomial.cyclotomic q A))) = 0 := by
  rw [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
    Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

private theorem unitDeriv {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    IsUnit (AdjoinRoot.mk (Polynomial.cyclotomic q A)
      (Polynomial.derivative (Polynomial.cyclotomic q A))) := by
  rcases subsingleton_or_nontrivial (AdjoinRoot (Polynomial.cyclotomic q A)) with h | h
  · exact isUnit_of_subsingleton _
  · have hq' : IsUnit ((q : ℕ) : AdjoinRoot (Polynomial.cyclotomic q A)) := by
      simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))
    have := LateralTheory.E.LeafClosedSH0PfPrim.derivUnit q _ hq' (evalRoot q)
    rwa [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
      Polynomial.derivative_map, Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq] at this

private theorem injOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at ha
  refine (Polynomial.cyclotomic.monic q A).not_dvd_of_degree_lt
    (Polynomial.C_ne_zero.2 h0) ?_ ha
  rw [Polynomial.degree_cyclotomic, Polynomial.degree_C h0]
  exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)

private theorem surjOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))) := by
  intro p
  have := (Polynomial.cyclotomic.monic q A).finite_adjoinRoot
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := AdjoinRoot (Polynomial.cyclotomic q A)) p.asIdeal ⊥ (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (injOf q)]
      exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩

private noncomputable def rootPrim {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    Prim q (AdjoinRoot (Polynomial.cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))), by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact evalRoot q⟩

theorem UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}), IsUnit ((q : ℕ) : Γ(X, ⊤)) → ∀ x : X, ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (_ : Prim q Γ(V, ⊤)), f y = x := by
  intro q _ X hq x
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨p, hp⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
  have hnt : Nontrivial Γ(X, W) := by
    rcases subsingleton_or_nontrivial Γ(X, W) with h | h
    · exact absurd (Subsingleton.elim _ _) p.2.ne_top
    · exact h
  have hqW : IsUnit ((q : ℕ) : Γ(X, W)) := by
    simpa using hq.map (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  have het : Algebra.Etale Γ(X, W) (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    GlobalTheory.etale_adjoinRoot_of_isUnit_derivative (Polynomial.cyclotomic.monic q _) (unitDeriv q hqW)
  let φ : CommRingCat.of Γ(X, W) ⟶ CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 het)
  obtain ⟨y0, hy0⟩ := surjOf (A := Γ(X, W)) q p
  let y : Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))) := y0
  have hy : Spec.map φ y = p := hy0
  refine ⟨Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))),
    Spec.map φ ≫ hW.fromSpec, inferInstance, y,
    Prim.map (Scheme.ΓSpecIso _).inv.hom (rootPrim q hqW), ?_⟩
  rw [Scheme.Hom.comp_apply, hy, hp]
