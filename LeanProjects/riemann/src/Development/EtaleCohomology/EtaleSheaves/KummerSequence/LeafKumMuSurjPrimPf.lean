import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf

open Polynomial CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
noncomputable section
namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf

theorem cyc_cond (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    ∃ p₁ p₂ : B[X], ∃ n : ℕ, derivative (cyclotomic q B) * p₁ + cyclotomic q B * p₂ = (1 : B[X]) ^ n := by
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q B
  obtain ⟨c, hc⟩ : ∃ c : B, c * q = 1 := ⟨↑hq.unit⁻¹, by simp⟩
  refine ⟨C c * X * G, C c * X * derivative G - G, 1, ?_⟩
  have hd := congrArg derivative hG
  rw [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero] at hd
  have key : (1 : B[X]) = C c * X * (C (q : B) * X ^ (q - 1)) - (X ^ q - 1) := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp at hc; have : Subsingleton B := subsingleton_of_zero_eq_one hc; exact Subsingleton.elim _ _
    · have : X * X ^ (q - 1) = (X : B[X]) ^ q := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      calc (1 : B[X]) = C (c * q) * (X * X ^ (q - 1)) - (X ^ q - 1) := by rw [hc, this]; simp
        _ = _ := by rw [C_mul]; ring
  rw [pow_one, key, hd, hG]
  ring

def cycPair (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) : StandardEtalePair B where
  f := cyclotomic q B
  monic_f := cyclotomic.monic q B
  g := 1
  cond := cyc_cond q B hq

theorem cycPair_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q ℤ) = 0 := by
  have h : aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1
  rw [← map_cyclotomic_int, ← algebraMap_int_eq, aeval_map_algebraMap] at h
  exact h

theorem cycX_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1

theorem root_hasMap (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).HasMap (AdjoinRoot.root (cyclotomic q B)) := by
  refine ⟨?_, ?_⟩
  · show aeval _ (cyclotomic q B) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · show IsUnit (aeval _ (1 : B[X]))
    simp

def cycTo (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring →ₐ[B] AdjoinRoot (cyclotomic q B) :=
  (cycPair q B hq).lift _ (root_hasMap q B hq)

def cycFrom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    AdjoinRoot (cyclotomic q B) →ₐ[B] (cycPair q B hq).Ring :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) (cycPair q B hq).X
    (by exact (aeval_def _ _).symm.trans (cycX_root q B hq))

theorem cycFrom_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycFrom q B hq (AdjoinRoot.root _) = (cycPair q B hq).X := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem cycTo_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycTo q B hq (cycPair q B hq).X = AdjoinRoot.root _ := StandardEtalePair.lift_X _ _ _

def cycEquiv (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring ≃ₐ[B] AdjoinRoot (cyclotomic q B) :=
  AlgEquiv.ofAlgHom (cycTo q B hq) (cycFrom q B hq)
    (AdjoinRoot.algHom_ext (by
      show cycTo q B hq (cycFrom q B hq (AdjoinRoot.root _)) = AdjoinRoot.root _
      rw [cycFrom_root, cycTo_X]))
    ((cycPair q B hq).hom_ext (by
      show cycFrom q B hq (cycTo q B hq (cycPair q B hq).X) = (cycPair q B hq).X
      rw [cycTo_X, cycFrom_root]))

theorem cyc_comap_surj (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (cycPair q B hq).Ring)) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : IsEmpty (PrimeSpectrum B) := PrimeSpectrum.isEmpty_iff_subsingleton.2 hB
    intro x; exact isEmptyElim x
  · have hfree : Module.Free B (AdjoinRoot (cyclotomic q B)) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis
    have : Module.Free B (cycPair q B hq).Ring := Module.Free.of_equiv (cycEquiv q B hq).symm.toLinearEquiv
    have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hd : 0 < (cyclotomic q B).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero hq0)
    have : Nontrivial (AdjoinRoot (cyclotomic q B)) :=
      nontrivial_of_ne _ 0 ((AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis.ne_zero ⟨0, hd⟩)
    have : Nontrivial (cycPair q B hq).Ring := (cycEquiv q B hq).toEquiv.nontrivial
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem prim_of_hom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) {A : Type} [CommRing A]
    (ψ : (cycPair q B hq).Ring →+* A) : Nonempty (Prim q A) := by
  refine ⟨⟨ψ (cycPair q B hq).X, ?_, ?_⟩⟩
  · have h := (hq.map (algebraMap B (cycPair q B hq).Ring)).map ψ
    simpa using h
  · rw [show ψ (cycPair q B hq).X = ψ.toIntAlgHom (cycPair q B hq).X from rfl, Polynomial.aeval_algHom_apply, cycPair_X, map_zero]

theorem LeafKumMuSurjPrim_pf : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := by
  intro q _ B _ hq U hU
  let φ : CommRingCat.of B ⟶ CommRingCat.of (cycPair q B hq).Ring :=
    CommRingCat.ofHom (algebraMap B (cycPair q B hq).Ring)
  let x : U ⟶ Spec (CommRingCat.of B) := hU.some
  have hE : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.2 ((RingHom.etale_algebraMap (R := B) (S := (cycPair q B hq).Ring)).2 inferInstance)
  have hS : Surjective (Spec.map φ) := ⟨cyc_comap_surj q B hq⟩
  have hE' : Etale (pullback.fst x (Spec.map φ)) := inferInstance
  have hS' : Surjective (pullback.fst x (Spec.map φ)) := inferInstance
  refine ⟨Sieve.generate (Presieve.singleton (pullback.fst x (Spec.map φ))),
    Precoverage.generate_mem_toGrothendieck ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2 ⟨hS'.surj, hE'⟩), ?_⟩
  rintro V f ⟨W, g, _, ⟨⟩, rfl⟩
  exact prim_of_hom q B hq ((Scheme.Γ.map (g ≫ pullback.snd x (Spec.map φ)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (cycPair q B hq).Ring)).inv.hom)

theorem LeafKumMuSurjPrim_of : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := LeafKumMuSurjPrim_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf
