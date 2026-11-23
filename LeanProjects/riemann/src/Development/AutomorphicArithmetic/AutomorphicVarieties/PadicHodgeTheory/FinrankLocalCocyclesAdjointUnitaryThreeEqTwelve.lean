import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem wt_cases (a b : Fin 3) : ∃ j : Fin 5, wt a b = ((j : ℕ) : ℤ) - 2 := by
  revert a b; decide

private theorem sum_dim {E G : Type} [Field E] (S : Submodule E (G → Matrix (Fin 3) (Fin 3) E))
    [Module.Finite E S]
    (h : ∀ j : ℤ, ∀ γ ∈ S, (fun g => Matrix.of fun a b => if wt a b = j then γ g a b else 0) ∈ S) :
    finrank E S = ∑ j : Fin 5,
      finrank E ↥(S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)) := by
  classical
  let T : Fin 5 → Submodule E (G → Matrix (Fin 3) (Fin 3) E) := fun j =>
    S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)
  haveI : ∀ j, Module.Finite E (T j) := fun j => Submodule.finiteDimensional_of_le (inf_le_left : T j ≤ S)
  let f : (∀ j, T j) →ₗ[E] S :=
    { toFun := fun x => ⟨∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E), S.sum_mem fun j _ => (x j).2.1⟩
      map_add' := fun x y => by ext1; simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by ext1; simp [Finset.smul_sum] }
  have hinj : ∀ i j : Fin 5, ((i : ℕ) : ℤ) - 2 = ((j : ℕ) : ℤ) - 2 → i = j := fun i j hij =>
    Fin.ext (by omega)
  have hval : ∀ (x : ∀ j, T j) (g : G) (a b : Fin 3) (j : Fin 5), wt a b = ((j : ℕ) : ℤ) - 2 →
      (f x : G → Matrix (Fin 3) (Fin 3) E) g a b = (x j : G → Matrix (Fin 3) (Fin 3) E) g a b := by
    intro x g a b j hj
    change (∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E)) g a b = _
    rw [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_eq_single j (fun i _ hi => ?_) (by simp)
    exact (x i).2.2 g trivial a b fun hh => hi (hinj _ _ (hh.symm.trans hj))
  have hb : Function.Bijective f := by
    constructor
    · intro x y hxy
      funext j
      apply Subtype.ext
      funext g
      ext a b
      by_cases hj : wt a b = ((j : ℕ) : ℤ) - 2
      · rw [← hval x g a b j hj, ← hval y g a b j hj, hxy]
      · rw [(x j).2.2 g trivial a b hj, (y j).2.2 g trivial a b hj]
    · intro γ
      refine ⟨fun j => ⟨_, h (((j : ℕ) : ℤ) - 2) γ γ.2, fun g _ a b hab => ?_⟩, ?_⟩
      · simp only [Matrix.of_apply, if_neg hab]
      · apply Subtype.ext
        funext g
        ext a b
        obtain ⟨j, hj⟩ := wt_cases a b
        rw [hval _ g a b j hj]
        simp only [Matrix.of_apply, if_pos hj]
  rw [← (LinearEquiv.ofBijective f hb).finrank_eq, Module.finrank_pi_fintype]

theorem UpperTheory.finrank_local_cocycles_adjoint_unitaryThree_eq_twelve :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], finrank E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) = 12 := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _
  have H := fun j => UpperTheory.V.Loc.dim_Z1f_crystalline_deformation hP D E j
  haveI := (H 0).1
  rw [sum_dim _ fun j => (H j).2.2.1, Finset.sum_congr rfl fun j _ => (H _).2.1]
  decide
