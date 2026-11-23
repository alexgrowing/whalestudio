import Formalism.CharacterColumnKernels.StatOntoLattice

open Module

noncomputable section

namespace Formalism.NG

theorem burnside : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm

theorem ontoLattice : StatOntoLattice := by
  intro O A L _ _ _ _ _ _ _ _ φ hφ
  have hle : (⊤ : Submodule O (Module.End O L)) ≤
      LinearMap.range φ.toLinearMap ⊔ IsLocalRing.maximalIdeal O • ⊤ := by
    intro f _
    obtain ⟨a, ha⟩ := hφ f
    have hf : f = φ a + (f - φ a) := by abel
    rw [hf]
    exact Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨a, rfl⟩) ha
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  intro f
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (htop Submodule.mem_top)
  exact ⟨a, ha⟩

section RankMod

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

private theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hproj : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  have hfin : Module.Finite O p :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl p q h) (fun x => ⟨x, Submodule.linearProjOfIsCompl_apply_left h x⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

private theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let f : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hf : f * f = f := by
    show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he.eq]
  have hc : IsCompl (LinearMap.range f) (LinearMap.ker f) :=
    LinearMap.IsIdempotentElem.isCompl hf
  obtain ⟨hpF, hpFin⟩ := free_of_isCompl _ _ hc
  obtain ⟨hqF, hqFin⟩ := free_of_isCompl _ _ hc.symm
  let bp := Module.Free.chooseBasis O (LinearMap.range f)
  let bq := Module.Free.chooseBasis O (LinearMap.ker f)
  let b0 := (bp.prod bq).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let σ := b0.indexEquiv (Pi.basisFun O r)
  let b := b0.reindex σ
  have hfb : ∀ j, f (b j) = (if (σ.symm j).isLeft then (1 : O) else 0) • b j := by
    intro j
    rw [Basis.reindex_apply]
    rcases σ.symm j with k | k
    · have hk : (b0 (Sum.inl k) : r → O) = (bp k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inl, if_true, one_smul, hk]
      obtain ⟨y, hy⟩ := (bp k).2
      rw [← hy]
      show (f * f) y = f y
      rw [hf]
    · have hk : (b0 (Sum.inr k) : r → O) = (bq k : r → O) := by
        simp [b0, Basis.map_apply, Basis.prod_apply]
      simp only [Sum.isLeft_inr, Bool.false_eq_true, if_false, zero_smul, hk]
      exact LinearMap.mem_ker.mp (bq k).2
  have hdiag : LinearMap.toMatrix b b f =
      Matrix.diagonal fun i => if (σ.symm i).isLeft then (1 : O) else 0 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hfb, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨(Pi.basisFun O r).toMatrix b, b.toMatrix (Pi.basisFun O r),
    fun i => if (σ.symm i).isLeft then (1 : O) else 0,
    fun j => by by_cases h : (σ.symm j).isLeft <;> simp [h],
    Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  rw [← hdiag, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
    LinearMap.toMatrix_eq_toMatrix']
  exact (LinearMap.toMatrix'_toLin' e).symm

private theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  have hm1 : P.map f * Q.map f = 1 := by
    rw [← Matrix.map_mul, hPQ]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hm2 : Q.map f * P.map f = 1 := by
    rw [← Matrix.map_mul, hQP]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm2),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hm1),
    Matrix.diagonal_map (map_zero f), Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro j
  constructor
  · intro h
    rcases hd j with h0 | h1
    · exact (h (by rw [h0, map_zero])).elim
    · exact h1
  · intro h1
    rw [h1, map_one]
    exact one_ne_zero

end RankMod

theorem rankMod : StatRankMod := by
  intro O _ _ _ r _ _ e he
  obtain ⟨P, Q, d, hd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  rw [rank_map_conj _ P Q d hd hPQ hQP, rank_map_conj _ P Q d hd hPQ hQP]

end Formalism.NG
