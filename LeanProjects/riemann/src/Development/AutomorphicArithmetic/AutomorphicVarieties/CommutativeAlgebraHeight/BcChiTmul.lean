import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem bc_D {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [inst : Algebra A S] [h : IsScalarTower A B S]
    (y : S ⊗[B] (B ⊗[A] E)) : (D.baseChange B).D S y = D.D S (Det.cancel A E B S y) := by
  have e : inst = ((algebraMap B S).comp (algebraMap A B)).toAlgebra :=
    Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A B S a
  subst e
  rfl

private theorem cancel_one {A E : Type} [CommRing A] [Ring E] [Algebra A E] (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (y : B ⊗[A] E) : Det.cancel A E B S (1 ⊗ₜ y) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B S) (AlgHom.id A E) y := by
  induction y with
  | zero => simp
  | tmul b z => simp [Det.cancel_tmul]
  | add a b ha hb => simp only [tmul_add, map_add, ha, hb]

private theorem bc_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (y : B ⊗[A] E) : (D.baseChange B).chi y = D.chiS B y := by
  unfold Det.chi Det.chiS
  rw [bc_D, map_sub, cancel_one, Algebra.TensorProduct.one_def, Det.cancel_tmul, map_one, mul_one]

private theorem bc_chi_tmul {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (x : E) : (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) := by
  rw [bc_chi]
  have h := D.nat A[X] B[X] (Polynomial.mapAlgHom (Algebra.ofId A B)) (X ⊗ₜ 1 - 1 ⊗ₜ x)
  unfold Det.chi Det.chiS
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    simp
  · rfl

theorem UpperTheory.V.CA.d_bc :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type) [CommRing B] [Algebra A B], (∀ (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (y : S ⊗[B] (B ⊗[A] E)), (D.baseChange B).D S y = D.D S (Det.cancel A E B S y)) ∧ (∀ y, (D.baseChange B).val y = D.D B y) ∧ (∀ y, (D.baseChange B).chi y = D.chiS B y) ∧ ∀ x : E, (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) ∧ ∀ i, (D.baseChange B).lam i (1 ⊗ₜ x) = algebraMap A B (D.lam i x) := by
  intro n A E _ _ _ D B _ _
  refine ⟨fun S _ _ _ _ y => bc_D D B S y, fun y => ?_, bc_chi D B, fun x => ⟨bc_chi_tmul D B x, fun i => ?_⟩⟩
  · change (D.baseChange B).D B (1 ⊗ₜ y) = _
    rw [bc_D, cancel_one]
    congr 1
    induction y with
    | zero => simp
    | tmul b z => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  · unfold Det.lam
    rw [bc_chi_tmul, Polynomial.coeff_map]
    simp
