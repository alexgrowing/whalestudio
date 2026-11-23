import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem spanO_gen {O K : Type} [CommRing O] [Field K] (f : O →+* K) {n : ℕ} (ι : Type)
    (r : ι → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span K (Set.range fun i => (r i).map f) = ⊤) :
    ∃ a : O, a ≠ 0 ∧ ∀ Z : Matrix (Fin n) (Fin n) O, a • Z ∈ Submodule.span O (Set.range r) := by
  classical
  obtain ⟨κ, g, -, hsp, hli⟩ := exists_linearIndependent' K (fun i => (r i).map f)
  rw [h] at hsp
  let b := Module.Basis.mk hli hsp.ge
  haveI : Finite κ := Module.Finite.finite_basis b
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin n × Fin n) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_matrix]
    simp
  let e : Fin n × Fin n ≃ κ := Fintype.equivOfCardEq hcard
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) O := fun p q => r (g (e q)) p.1 p.2
  have hM : f M.det ≠ 0 := by
    rw [RingHom.map_det]
    have hli2 : LinearIndependent K (f.mapMatrix M).col := by
      have hl := (hli.comp e e.injective).map' (LinearEquiv.curry K K (Fin n) (Fin n)).symm.toLinearMap (LinearEquiv.ker _)
      have heq : (f.mapMatrix M).col = (LinearEquiv.curry K K (Fin n) (Fin n)).symm.toLinearMap ∘ ((fun i => (r i).map f) ∘ g) ∘ e := by
        funext q p
        rfl
      rw [heq]
      exact hl
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli2)).ne_zero
  refine ⟨M.det, fun h0 => hM (by rw [h0, map_zero]), fun Z => ?_⟩
  let v : Fin n × Fin n → O := fun p => Z p.1 p.2
  let w := M.adjugate *ᵥ v
  have hw : M *ᵥ w = M.det • v := by
    simp only [w, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
    first
      | simp [Matrix.smul_mulVec]
      | (ext p; simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply])
  have hZ : M.det • Z = ∑ q, w q • r (g (e q)) := by
    ext i j
    have hij := congrFun hw (i, j)
    simp only [Matrix.mulVec, dotProduct, M, v, Pi.smul_apply, smul_eq_mul] at hij
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← hij]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hZ]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem UpperTheory.V.Th.Nm.spanO :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (c : Coef l) (ι : Type) (r : ι → Matrix (Fin n) (Fin n) c.O), Submodule.span (Qbar l) (Set.range fun i => (r i).map (algebraMap c.O (Qbar l))) = ⊤ → ∃ a : c.O, a ≠ 0 ∧ ∀ Z : Matrix (Fin n) (Fin n) c.O, a • Z ∈ Submodule.span c.O (Set.range r) := by
  intro l _ n c ι r h
  exact spanO_gen (algebraMap c.O (Qbar l)) ι r h
