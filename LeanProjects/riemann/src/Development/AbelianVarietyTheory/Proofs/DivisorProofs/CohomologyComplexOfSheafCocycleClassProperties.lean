import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCElements

theorem chains_X_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) :=
  ((chainsN R).obj E).isZero_extend_X ComplexShape.embeddingDownNat n (fun i hi => by
    change -(i : ℤ) = n at hi; omega)

theorem res_X_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spcᵒᵖ) (n : ℤ), n < 0 → IsZero (((HC R F).obj E).X n)) ∧ ∃ cl : ∀ (E : Spc) (n : ℤ) (z : ((HC R F).obj (op E)).X n), ((HC R F).obj (op E)).d n (n + 1) z = 0 → H R E F n, (∀ E n x, ∃ z hz, cl E n z hz = x) ∧ (∀ E n z hz z' hz', cl E n z hz = cl E n z' hz' ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = z' + ((HC R F).obj (op E)).d (n - 1) n y) ∧ (∀ E n z hz, cl E n z hz = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), z = ((HC R F).obj (op E)).d (n - 1) n y) ∧ ∀ (E E' : Spc) (f : E ⟶ E') n z hz, ∃ h, pull R f F n (cl E' n z hz) = cl E n (((HC R F).map f.op).f n z) h := by
  intro R _ F
  have zero_iff : ∀ (E : Spc) (n : ℤ) (c : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk c = 0 ↔ ∃ y : ((HC R F).obj (op E)).X (n - 1), (show ((HC R F).obj (op E)).X n from c.1) = ((HC R F).obj (op E)).d (n - 1) n y := by
    intro E n c
    rw [CohomologyClass.mk_eq_zero_iff]
    constructor
    · rintro ⟨m, hm, β, hβ⟩
      obtain rfl : m = n - 1 := by omega
      exact ⟨β, hβ.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨n - 1, by omega, y, hy.symm⟩
  refine ⟨?_, fun E n z hz => CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz), ?_, ?_, ?_, ?_⟩
  · intro E n hn
    refine @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => ?_⟩
    change Cochain ((chains R).obj E.unop) (res R F) n at a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : 0 < p
    · exact (chains_X_isZero R E.unop p hp).eq_of_src _ _
    · exact (res_X_isZero R F q (by omega)).eq_of_tgt _ _
  · intro E n x
    obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c.1, c.2, rfl⟩
  · intro E n z hz z' hz'
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _ at hy
      rw [← hy]; abel
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change z - z' = _
      rw [hy]; abel
  · intro E n z hz
    exact zero_iff E n _
  · intro E E' f n z hz
    refine ⟨(zcomp (Cocycle.ofHom ((chains R).map f)) (Cocycle.mk z (n + 1) rfl hz) (zero_add n)).2, ?_⟩
    rfl

end GlobalTheory.EtC.HCElements
