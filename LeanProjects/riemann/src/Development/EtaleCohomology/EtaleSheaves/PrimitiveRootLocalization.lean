import Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.PrimitiveRootLocalization

theorem cyc_cond {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ (p₁ p₂ : A[X]) (n : ℕ), derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = (1 : A[X]) ^ n := by
  obtain ⟨h, e1⟩ := cyclotomic.dvd_X_pow_sub_one q A
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  have e2 := congrArg derivative e1
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at e2
  have e3 : C v * C (q : A) = 1 := by rw [← C_mul, hv, C_1]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have e4 : X * X ^ (q - 1) = (X : A[X]) ^ q := by rw [← pow_succ']; congr 1; omega
  refine ⟨C v * X * h, C v * X * derivative h - h, 0, ?_⟩
  linear_combination (-(C v * X)) * e2 + (C v * C (q : A)) * e4 + X ^ q * e3 + e1

def cycPair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := cyc_cond q hq

section
variable {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A))

theorem cycPair_hasMap_root : (cycPair q hq).HasMap (AdjoinRoot.root (cyclotomic q A)) := by
  refine ⟨?_, ?_⟩
  · simp [cycPair]
  · simp [cycPair]

theorem adjoinRoot_nontrivial [Nontrivial A] : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (cyclotomic.monic q A).isUnit_iff.mp hu
  have h2 := natDegree_cyclotomic q A
  rw [h1, natDegree_one] at h2
  exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne' h2.symm

theorem comap_surj : Function.Surjective (PrimeSpectrum.comap (algebraMap A (cycPair q hq).Ring)) := by
  by_cases hA : Nontrivial A
  · let ψ : (cycPair q hq).Ring →ₐ[A] AdjoinRoot (cyclotomic q A) := (cycPair q hq).lift _ (cycPair_hasMap_root q hq)
    have := (cyclotomic.monic q A).free_adjoinRoot
    have := adjoinRoot_nontrivial (A := A) q
    have hs := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := AdjoinRoot (cyclotomic q A))
    have e : algebraMap A (AdjoinRoot (cyclotomic q A)) = (ψ : (cycPair q hq).Ring →+* _).comp (algebraMap A (cycPair q hq).Ring) := by
      ext a; simp
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨PrimeSpectrum.comap (ψ : (cycPair q hq).Ring →+* _) y, ?_⟩
    rw [← hy, e]
    rfl
  · intro x
    rw [not_nontrivial_iff_subsingleton] at hA
    exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

def primRing : Prim q (cycPair q hq).Ring :=
  ⟨(cycPair q hq).X, by simpa using hq.map (algebraMap A (cycPair q hq).Ring), by
    have h := (cycPair q hq).hasMap_X.1
    change aeval (cycPair q hq).X (cyclotomic q A) = 0 at h
    rw [← map_cyclotomic q (algebraMap ℤ A), aeval_map_algebraMap] at h
    exact h⟩

end

theorem LeafPrimLoc_of : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := by
  intro q _ U hq
  let P := cycPair (A := Γ(U, ⊤)) q hq
  let f : Spec (CommRingCat.of P.Ring) ⟶ Spec Γ(U, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) P.Ring))
  have hfe : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hfs : Surjective f := ⟨comap_surj q hq⟩
  have hge : Etale (pullback.fst U.toSpecΓ f) := inferInstance
  have hgs : Surjective (pullback.fst U.toSpecΓ f) := inferInstance
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (Prim q Γ(V, ⊤))
      downward_closed := fun {V W} g hg h => hg.elim fun ζ => ⟨Prim.map h.appTop.hom ζ⟩ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hgs.surj, hge⟩))
  rintro V _ ⟨W, h, k, ⟨⟩, rfl⟩
  exact ⟨Prim.map ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv ≫ (h ≫ pullback.snd _ _).appTop).hom (primRing q hq)⟩

end LateralTheory.E.PrimitiveRootLocalization
