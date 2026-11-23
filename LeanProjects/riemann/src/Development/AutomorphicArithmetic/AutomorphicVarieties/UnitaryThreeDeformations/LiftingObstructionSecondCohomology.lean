import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition {O M : Type} [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    [Finite M] (hM : ∀ a ∈ maximalIdeal O, ∀ x : M, a • x = 0) :
    ∃ (n : ℕ) (p : Fin n → M →ₗ[O] ResidueField O) (q : Fin n → ResidueField O →ₗ[O] M),
      ∀ x, ∑ i, q i (p i x) = x := by
  have hT : Module.IsTorsionBySet O M (maximalIdeal O) := fun x a => hM a.1 a.2 x
  letI : Module (ResidueField O) M := hT.module
  haveI : IsScalarTower O (ResidueField O) M := hT.isScalarTower
  haveI : Module.Finite (ResidueField O) M := Module.Finite.of_finite
  let B := Module.finBasis (ResidueField O) M
  refine ⟨_, fun i => (B.coord i).restrictScalars O,
    fun i => (LinearMap.toSpanSingleton (ResidueField O) M (B i)).restrictScalars O, fun x => ?_⟩
  simpa using B.sum_repr x

private theorem UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (X : Matrix (Fin 3) (Fin 3) S) (a b : Fin 3) :
    adRep (r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ)) g X a b =
      ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then X a b else -X b.rev a.rev) := by
  rw [adRep_baseLift_apply, Algebra.smul_def, MonoidHom.comp_apply, ← map_zpow]
  rfl

private theorem UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) :
    (GG.map (algebraMap O S)).comp (r0 η Ψ) = r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ) := by
  ext g i j
  · simp [r0, GG.map]
    rw [tor_val, tor_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [← map_zpow, ← map_zpow, Units.coe_map, map_zpow]
      rfl
    · simp
  · simp [r0, GG.map]

private theorem UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary {k D : Type} [CommRing k] [Group D] [TopologicalSpace D]
    (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (h : Subsingleton (H2 (gRep η Ψ j)))
    (κ : D × D → Matrix (Fin 3) (Fin 3) k) (hc : IsLocallyConstant κ) (hw : ∀ z, κ z ∈ gw k j)
    (hκ : ∀ g h l, adRep (r0 η Ψ) g (κ (h, l)) - κ (g * h, l) + κ (g, h * l) - κ (g, h) = 0) :
    ∃ b : D → Matrix (Fin 3) (Fin 3) k, IsLocallyConstant b ∧ (∀ g, b g ∈ gw k j) ∧
      ∀ g h, κ (g, h) = adRep (r0 η Ψ) g (b h) - b (g * h) + b g := by
  let f : D × D → Gb k j := fun z => (⟨κ z, hw z⟩ : ↥(gw k j))
  have hfl : IsLocallyConstant f :=
    IsLocallyConstant.desc f (fun x : Gb k j => (x.val : Matrix (Fin 3) (Fin 3) k)) hc
      (fun x y hxy => Subtype.ext hxy)
  have hf : f ∈ Z2 (gRep η Ψ j) := by
    refine (mem_cocycles2 _ _).2 ⟨hfl.continuous, fun g h l => ?_⟩
    apply Subtype.ext
    exact hκ g h l
  have h0 : (Submodule.Quotient.mk ⟨f, hf⟩ : H2 (gRep η Ψ j)) = 0 := Subsingleton.elim _ _
  have hB : f ∈ B2 (gRep η Ψ j) := by
    have := (Submodule.Quotient.mk_eq_zero ((B2 (gRep η Ψ j)).comap (Z2 (gRep η Ψ j)).subtype)
      (x := ⟨f, hf⟩)).1 h0
    simpa using this
  obtain ⟨c, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  refine ⟨fun g => (c g).val, ((IsLocallyConstant.iff_continuous c).2 hcc).comp _,
    fun g => (c g).2, fun g h => ?_⟩
  have e := congrArg (fun x : Gb k j => x.val) (congrFun hd (g, h))
  rw [d1_apply] at e
  exact e.symm

theorem UpperTheory.V.UnitaryThreeInertia.lifting_obstruction_second_cohomology :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ κ : D × D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant κ → (∀ z, κ z ∈ gw R j) → (∀ z, EntIn K (κ z)) →
      (∀ g h k, adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (κ (h, k)) - κ (g * h, k) + κ (g, h * k) - κ (g, h) = 0) →
      ∃ b : D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant b ∧ (∀ g, b g ∈ gw R j) ∧ (∀ g, EntIn K (b g)) ∧
        ∀ g h, κ (g, h) = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (b h) - b (g * h) + b g := by
  classical
  intro O R D _ _ _ _ _ _ _ _ η Ψ K j hK hH κ hc hw hE hκ
  have memgw : ∀ (S : Type) [CommRing S] (X : Matrix (Fin 3) (Fin 3) S),
      X ∈ gw S j ↔ ∀ a b, ¬ wt a b = j → X a b = 0 := by
    intro S _ X
    unfold gw
    rfl
  have hloc : IsLocalHom (algebraMap O R) := by
    obtain ⟨_, hl, _⟩ := ‹IsCO O R›
    exact hl
  let KO : Submodule O R := K.restrictScalars O
  have hM : ∀ a ∈ maximalIdeal O, ∀ x : KO, a • x = 0 := by
    intro a ha x
    apply Subtype.ext
    have h1 : algebraMap O R a ∈ maximalIdeal R := map_nonunit (algebraMap O R) a ha
    have h2 : algebraMap O R a * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul h1 x.2
    rw [hK] at h2
    simpa [Algebra.smul_def] using h2
  obtain ⟨n, p, q, hpq⟩ := UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition hM
  rw [UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra] at hκ ⊢
  have hE' : ∀ z a b, κ z a b ∈ KO := fun z a b => hE z a b
  let κK : D × D → Fin 3 → Fin 3 → KO := fun z a b => ⟨κ z a b, hE' z a b⟩
  have hres : (Units.map (residue O).toMonoidHom).comp Ψ =
      (Units.map (algebraMap O (ResidueField O)).toMonoidHom).comp Ψ := rfl
  have key : ∀ i, ∃ b : D → Matrix (Fin 3) (Fin 3) (ResidueField O), IsLocallyConstant b ∧
      (∀ g, b g ∈ gw (ResidueField O) j) ∧ ∀ g h, Matrix.of (fun a c => p i (κK (g, h) a c)) =
        adRep (r0 η ((Units.map (residue O).toMonoidHom).comp Ψ)) g (b h) - b (g * h) + b g := by
    intro i
    refine UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary η ((Units.map (residue O).toMonoidHom).comp Ψ) j hH
      (fun z => Matrix.of (fun a c => p i (κK z a c))) ?_ ?_ ?_
    · let G : Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) (ResidueField O) :=
        fun X => Matrix.of fun a c => if h : X a c ∈ KO then p i ⟨X a c, h⟩ else 0
      have hG : (fun z => Matrix.of (fun a c => p i (κK z a c))) = G ∘ κ := by
        funext z
        ext a c
        simp [G, κK, hE' z a c]
      rw [hG]
      exact hc.comp G
    · intro z
      rw [memgw]
      intro a c hac
      have h0 : κK z a c = 0 := Subtype.ext ((memgw R (κ z)).1 (hw z) a c hac)
      simp [h0]
    · intro g h l
      ext a c
      have e := congrFun (congrFun (hκ g h l) a) c
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, Matrix.of_apply] at e ⊢
      rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] at e
      rw [hres, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
      have eK : ((Ψ g ^ wt a c : Oˣ) : O) • (if η g = 1 then κK (h, l) a c else -κK (h, l) c.rev a.rev) -
          κK (g * h, l) a c + κK (g, h * l) a c - κK (g, h) a c = 0 := by
        apply Subtype.ext
        split_ifs at e ⊢ <;> simpa [κK] using e
      have e2 := congrArg (p i) eK
      split_ifs at e2 ⊢ <;> simpa using e2
  choose bs hbl hbw hbe using key
  refine ⟨fun g => Matrix.of fun a c => ((∑ i, q i (bs i g a c) : KO) : R), ?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Filter.eventually_all.2 (fun i => (hbl i).eventually_eq x)] with y hy
    simp only [hy]
  · intro g
    rw [memgw]
    intro a c hac
    have h0 : ∀ i, bs i g a c = 0 := fun i => (memgw _ _).1 (hbw i g) a c hac
    simp [h0]
  · intro g
    unfold EntIn
    intro a c
    exact (∑ i, q i (bs i g a c)).2
  · intro g h
    ext a c
    have e : ∀ i, p i (κK (g, h) a c) = ((Ψ g ^ wt a c : Oˣ) : O) •
        (if η g = 1 then bs i h a c else -bs i h c.rev a.rev) - bs i (g * h) a c + bs i g a c := by
      intro i
      have e1 := congrFun (congrFun (hbe i g h) a) c
      rw [hres] at e1
      simpa only [Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] using e1
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
    simp only [Matrix.of_apply]
    have hx : κ (g, h) a c = ((κK (g, h) a c : KO) : R) := rfl
    rw [hx, ← hpq (κK (g, h) a c)]
    simp_rw [e]
    split_ifs <;> simp [map_add, map_sub, map_neg, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
