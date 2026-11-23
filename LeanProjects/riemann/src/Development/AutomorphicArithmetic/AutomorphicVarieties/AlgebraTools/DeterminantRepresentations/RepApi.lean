import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

namespace UpperTheory.V.AlgebraTools.Det

section
variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private theorem repAlg_single (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (g : G) (r : B) : GDet.repAlg ρ B (MonoidAlgebra.single g r) = r • (ρ g).map (algebraMap A B) := by
  unfold GDet.repAlg
  rw [MonoidAlgebra.lift_single]
  rfl

private theorem repAlg_map (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (y : MonoidAlgebra A G) :
    GDet.repAlg ρ B (MonoidAlgebra.mapRingHom G (algebraMap A B) y) = (GDet.repAlg ρ A y).map (algebraMap A B) := by
  induction y using MonoidAlgebra.induction_on with
  | of g =>
    simp [MonoidAlgebra.of_apply, repAlg_single]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i j
    simp
  | smul r x hx =>
    have hr : r • x = MonoidAlgebra.single 1 r * x := by
      rw [Algebra.smul_def]
      rfl
    have hm : MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single 1 r)
        = MonoidAlgebra.single 1 (algebraMap A B r) := by
      ext g
      simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, repAlg_single, repAlg_single, map_one]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem ofRep_D (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (x : MonoidAlgebra B G) : (GDet.ofRep ρ).D B x = (GDet.repAlg ρ B x).det := rfl

private theorem chi_eq (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly := by
  unfold GDet.chi
  rw [ofRep_D, ← Polynomial.algebraMap_eq, map_sub, repAlg_single, repAlg_map, map_one]
  rw [Matrix.charpoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]

private theorem chi_single (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  rw [chi_eq, repAlg_single]; simp

end

end UpperTheory.V.AlgebraTools.Det

theorem UpperTheory.V.AlgebraTools.Det.repApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    (∀ y, (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly) ∧
    (∀ g, (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly) ∧
    (0 < n → ∀ y, (GDet.ofRep ρ).tr y = (GDet.repAlg ρ A y).trace) ∧
    (∀ g, (GDet.ofRep ρ).lam n (MonoidAlgebra.single g 1) = (ρ g).det) ∧
    (∀ y, GDet.repAlg ρ A y = 0 → (GDet.ofRep ρ).Kills y) ∧
    (∀ {A' : Type} [CommRing A'] (f : A →+* A'), (GDet.ofRep ρ).map f = GDet.ofRep ((RingHom.mapMatrix f).toMonoidHom.comp ρ)) ∧
    (∀ {H : Type} [Group H] (φ : H →* G), (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ)) ∧
    (∀ (ρ' : G →* Matrix (Fin n) (Fin n) A) (P : GL (Fin n) A), (∀ g, (P : Matrix (Fin n) (Fin n) A) * ρ' g = ρ g * P) → GDet.ofRep ρ' = GDet.ofRep ρ) := by
  intro n A G _ _ ρ
  refine ⟨chi_eq ρ, chi_single ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hn y
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold GDet.tr GDet.lam
    rw [chi_eq, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  · intro g
    unfold GDet.lam
    rw [chi_single, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, Nat.sub_self]
  · intro y hy
    unfold GDet.Kills
    intro B _ _ h
    rw [ofRep_D, map_add, map_mul, repAlg_map, hy, Matrix.map_zero _ (map_zero _), mul_zero, add_zero, map_one,
      Matrix.det_one]
  · intro A' _ f
    refine GDet.ext fun B _ _ x => ?_
    unfold GDet.map
    dsimp only
    rw [ofRep_D, ofRep_D]
    congr 2
  · intro H _ φ
    refine GDet.ext fun B _ _ x => ?_
    unfold GDet.comap
    dsimp only
    rw [MonoidHom.comp_apply, ofRep_D, ofRep_D]
    congr 1
    show GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x) = GDet.repAlg (ρ.comp φ) B x
    induction x using MonoidAlgebra.induction_on with
    | of h =>
      simp [MonoidAlgebra.of_apply, repAlg_single, MonoidAlgebra.mapDomainRingHom]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by
        rw [Algebra.smul_def]
        rfl
      rw [hr, map_mul, map_mul, map_mul, hx]
      congr 1
      simp [repAlg_single, MonoidAlgebra.mapDomainRingHom]
  · intro ρ' P hP
    refine GDet.ext fun B _ _ x => ?_
    have key : ∀ y : MonoidAlgebra B G,
        (P : Matrix (Fin n) (Fin n) A).map (algebraMap A B) * GDet.repAlg ρ' B y
          = GDet.repAlg ρ B y * (P : Matrix (Fin n) (Fin n) A).map (algebraMap A B) := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g =>
        rw [MonoidAlgebra.of_apply, repAlg_single, repAlg_single, one_smul, one_smul,
          ← Matrix.map_mul, ← Matrix.map_mul, hP]
      | add y z hy hz =>
        rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hy, hz]
      | smul r y hy =>
        rw [map_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul, hy]
    have hd := congrArg Matrix.det (key x)
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (GDet.repAlg ρ B x))] at hd
    have hu : IsUnit (Matrix.det ((P : Matrix (Fin n) (Fin n) A).map (algebraMap A B))) := by
      rw [show ((P : Matrix (Fin n) (Fin n) A).map (algebraMap A B)).det
          = algebraMap A B (P : Matrix (Fin n) (Fin n) A).det from (RingHom.map_det _ _).symm]
      exact (Matrix.isUnits_det_units P).map _
    rw [ofRep_D, ofRep_D]
    exact hu.mul_left_cancel hd
