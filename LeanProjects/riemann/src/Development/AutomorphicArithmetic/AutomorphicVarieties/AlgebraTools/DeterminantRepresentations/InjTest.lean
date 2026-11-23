import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval

open Polynomial UpperTheory.V.W

private theorem injTest_mvInj {A : Type} [CommRing A] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    (f : ∀ x, A →+* K x) (hf : ∀ a, (∀ x, f x a = 0) → a = 0) {σ : Type} (P Q : MvPolynomial σ A)
    (h : ∀ x, MvPolynomial.map (f x) P = MvPolynomial.map (f x) Q) : P = Q := by
  ext β
  rw [← sub_eq_zero]
  refine hf _ fun x => ?_
  have := congrArg (MvPolynomial.coeff β) (h x)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this
  rw [map_sub, this, sub_self]

private theorem injTest_smul {R S G : Type} [CommRing R] [CommRing S] [Group G] (φ : R →+* S) (r : R)
    (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (r • z) = φ r • MonoidAlgebra.mapRingHom G φ z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | single g s => simp

private theorem injTest_comp {R S T G : Type} [CommRing R] [CommRing S] [CommRing T] [Group G]
    (φ : R →+* S) (ψ : S →+* T) (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ (MonoidAlgebra.mapRingHom G φ z) = MonoidAlgebra.mapRingHom G (ψ.comp φ) z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g s => simp

theorem UpperTheory.V.AlgebraTools.Det.injTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) →
    (∀ D D' : GDet n A G, (∀ x, D.map (f x) = D'.map (f x)) → D = D') ∧
    (∀ (D : GDet n A G) (y : MonoidAlgebra A G), (∀ x, (D.map (f x)).Kills (MonoidAlgebra.mapRingHom G (f x) y)) → D.Kills y) := by
  intro n A G _ _ X K _ f hf
  refine ⟨fun D D' h => ?_, fun D y h => ?_⟩
  · refine UpperTheory.V.AlgebraTools.Det.extGen D D' fun m g => ?_
    refine injTest_mvInj K f hf _ _ fun x => ?_
    rw [← (UpperTheory.V.AlgebraTools.Det.mapApi D (f x)).2.2.2.2.1, ← (UpperTheory.V.AlgebraTools.Det.mapApi D' (f x)).2.2.2.2.1, h x]
  · intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    set z : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
      1 + GDet.gen (fun j => MonoidAlgebra.single (g j) (1 : A)) * MonoidAlgebra.mapRingHom G MvPolynomial.C y with hz
    have h1 : D.D (MvPolynomial (Fin m) A) z = 1 := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← (UpperTheory.V.AlgebraTools.Det.mapApi D (f x)).2.2.2.1, map_one, hz, map_add, map_one, map_mul, injTest_comp]
      have e : (MvPolynomial.map (f x) : MvPolynomial (Fin m) A →+* _).comp MvPolynomial.C =
          (algebraMap (K x) (MvPolynomial (Fin m) (K x))).comp (f x) := by
        ext a : 1
        simp
      rw [e, ← injTest_comp]
      exact h x _ _
    have h2 := D.nat _ B (MvPolynomial.aeval b) z
    have e : ((MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B) : MvPolynomial (Fin m) A →+* B).comp
        MvPolynomial.C = algebraMap A B := by
      ext a : 1
      simp
    rw [h1, map_one, hz, map_add, map_one, map_mul, injTest_comp, e, GDet.gen, map_sum] at h2
    simp only [injTest_smul, injTest_comp, e] at h2
    simpa only [RingHom.coe_coe, MvPolynomial.aeval_X] using h2
