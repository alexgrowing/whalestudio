import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgCont

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prod_single {K α : Type} [CommRing K] (d : α → ℤ) (a : α → K) (L : List α) :
    (L.map fun s => AddMonoidAlgebra.single (d s) (a s)).prod =
      AddMonoidAlgebra.single (L.map d).sum (L.map a).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih, AddMonoidAlgebra.single_mul_single, List.map_cons,
      List.map_cons, List.sum_cons, List.prod_cons]

private theorem alg_val {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K)
    [SetLike.GradedMonoid P] (c : C) :
    (algebraMap C (lauSub P) c).1 = AddMonoidAlgebra.single 0 (algebraMap C K c) := by
  rfl

private theorem w_ne_w_of_ne (n : ℕ) {i j : Fin n} (hij : i ≠ j) : w n i ≠ w n j := by
  intro h
  apply hij
  unfold w at h
  split_ifs at h <;> exact Fin.ext (by omega)

theorem UpperTheory.V.Fr.alg_model :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → IsModel O C (vertex h) ρD := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  have key : ∀ (c : C) (y : K), algebraMap C K c = y → ∀ p : lauSub (ρ.part C),
      p.1 = AddMonoidAlgebra.single 0 y → algebraMap C (lauSub (ρ.part C)) c = p := by
    intro c y hcy p hp
    apply Subtype.ext
    rw [alg_val, hp, hcy]
  refine ⟨alg_cont C ρ hc h ρD hr hψ, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [mem_vertex]
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [hr, map_zero]
    have hne : (0 : ℤ) ≠ w n i - w n j := by
      intro h0
      exact w_ne_w_of_ne n hij (by omega)
    exact (Finsupp.single_eq_of_ne hne).symm
  · intro g i
    obtain ⟨c, hc1, hc2⟩ := hc.dg g i
    refine ⟨c, key c _ hc1 _ ?_, hc2⟩
    rw [hr, sub_self]
  · intro v i g
    obtain ⟨χ, hχ, hχψ⟩ := hc.psi
    exact ⟨χ v i g, key _ _ (hχψ v i g) _ (hψ v i g), (hχ v i).2 g⟩
  · intro x hx
    obtain ⟨L, hL, rfl⟩ := hx
    have hmem : (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ ρ.part C 0 :=
      Submodule.subset_span ⟨L, hL, rfl⟩
    obtain ⟨c, hc'⟩ := h.zero _ hmem
    refine ⟨c, key c _ hc' _ ?_⟩
    have e1 : ∀ L' : List (F.G0 × Fin n × Fin n),
        ((L'.map fun s => ρD.r s.1 s.2.1 s.2.2).prod : lauSub (ρ.part C)).1 =
          (L'.map fun s => AddMonoidAlgebra.single (w n s.2.1 - w n s.2.2) (ρ.r s.1 s.2.1 s.2.2)).prod := by
      intro L'
      induction L' with
      | nil => rfl
      | cons s L' ih =>
        rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, hr, List.map_cons, List.prod_cons]
    rw [e1, prod_single (fun s : F.G0 × Fin n × Fin n => w n s.2.1 - w n s.2.2)
      (fun s => ρ.r s.1 s.2.1 s.2.2) L, hL]
