import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

private theorem len_mid {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (h : N →ₗ[R] P)
    (e : Function.Exact f h) :
    Module.length R N = Module.length R (LinearMap.range f) + Module.length R (LinearMap.range h) := by
  refine Module.length_eq_add_of_exact (LinearMap.range f).subtype h.rangeRestrict
    (Submodule.injective_subtype _) h.surjective_rangeRestrict ?_
  intro n
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
  change h n = 0 ↔ _
  rw [e n]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨⟨f m, m, rfl⟩, rfl⟩
  · rintro ⟨⟨_, m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

private def tmap {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N) :
    Submodule.torsionBy R M g →ₗ[R] Submodule.torsionBy R N g :=
  f.restrict fun x hx => by
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    rw [← map_smul, hx, map_zero]

private theorem ex_tors {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (Submodule.torsionBy R M g).subtype (g • (LinearMap.id : M →ₗ[R] M)) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, rfl⟩
    simpa using hx
  · rintro ⟨⟨y, hy⟩, rfl⟩
    simpa using (Submodule.mem_torsionBy_iff _ _).1 hy

private theorem ex_quot {R : Type} (M : Type) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (g • (LinearMap.id : M →ₗ[R] M)) (g • (⊤ : Submodule R M)).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact ⟨b, by simp⟩
  · rintro ⟨b, rfl⟩
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, Submodule.mem_top, by simp⟩

theorem UpperTheory.V.abelian₂.snake_len :
    ∀ (R : Type) [CommRing R] (g : R) (A B D : Type) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D] [Module R D]
      (i : A →ₗ[R] B) (j : B →ₗ[R] D), Function.Injective i → Function.Surjective j → Function.Exact i j →
      invLen g A + invLen g D + coinvLen g B = invLen g B + coinvLen g A + coinvLen g D ∧
        invLen g B ≤ invLen g A + invLen g D ∧ coinvLen g B ≤ coinvLen g A + coinvLen g D ∧
        invLen g A ≤ invLen g B ∧ coinvLen g D ≤ coinvLen g B ∧
        coinvLen g A ≤ invLen g D + coinvLen g B ∧ invLen g D ≤ invLen g B + coinvLen g A := by
  intro R _ g A B D _ _ _ _ _ _ i j hi hj hij
  have h₁ : i ∘ₗ (g • LinearMap.id : A →ₗ[R] A) = (g • LinearMap.id : B →ₗ[R] B) ∘ₗ i := by
    ext a
    simp
  have h₂ : j ∘ₗ (g • LinearMap.id : B →ₗ[R] B) = (g • LinearMap.id : D →ₗ[R] D) ∘ₗ j := by
    ext b
    simp
  let G : QuotSMulTop g A →ₗ[R] QuotSMulTop g B := Submodule.mapQ _ _ i (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  let H : QuotSMulTop g B →ₗ[R] QuotSMulTop g D := Submodule.mapQ _ _ j (by
    intro a ha
    rw [Submodule.mem_comap]
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hG : G ∘ₗ (g • ⊤ : Submodule R A).mkQ = (g • ⊤ : Submodule R B).mkQ ∘ₗ i := by
    ext a
    rfl
  have hδr := SnakeLemma.exact_δ'_right (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂ (Submodule.torsionBy R B g).subtype (ex_tors B g)
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    hj hi (tmap g j) (by ext x; rfl) (Submodule.injective_subtype _)
  have hδl := SnakeLemma.exact_δ'_left (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    (g • ⊤ : Submodule R B).mkQ (ex_quot B g) hj hi G hG (Submodule.mkQ_surjective _)
  have e1 : Function.Exact (tmap g i) (tmap g j) := by
    intro x
    constructor
    · intro hx
      have hx' : j x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hij x.1).1 hx'
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      rw [Submodule.mem_torsionBy_iff]
      apply hi
      rw [map_smul, ha, map_zero]
      exact (Submodule.mem_torsionBy_iff _ _).1 x.2
    · rintro ⟨a, rfl⟩
      exact Subtype.ext (hij.apply_apply_eq_zero a.1)
  have i1 : Function.Injective (tmap g i) := fun x y hxy =>
    Subtype.ext (hi (congrArg Subtype.val hxy))
  have e4 : Function.Exact G H := by
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro hy
      change Submodule.Quotient.mk (j b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨d, -, hd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      obtain ⟨b', rfl⟩ := hj d
      obtain ⟨a, ha⟩ := (hij (b - g • b')).1 (by rw [map_sub, map_smul, hd, sub_self])
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (i a) = Submodule.Quotient.mk b
      rw [ha, Submodule.Quotient.eq, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
      change Submodule.Quotient.mk (j (i a)) = 0
      rw [hij.apply_apply_eq_zero, Submodule.Quotient.mk_zero]
  have s4 : Function.Surjective H := by
    intro y
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨b, rfl⟩ := hj d
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have L1 := len_mid (tmap g i) (tmap g j) e1
  have L2 := len_mid _ _ hδr
  have L3 := len_mid _ _ hδl
  have L4 := len_mid G H e4
  have r1 : Module.length R (LinearMap.range (tmap g i)) =
      Module.length R (Submodule.torsionBy R A g) :=
    (LinearEquiv.ofInjective _ i1).length_eq.symm
  have r4 : Module.length R (LinearMap.range H) = Module.length R (QuotSMulTop g D) := by
    rw [LinearMap.range_eq_top.2 s4, Module.length_top]
  have arith : ∀ p x y z q : ℕ∞,
      p + (x + y) + (z + q) = p + x + (y + z) + q ∧ p + x ≤ p + (x + y) ∧
        z + q ≤ y + z + q ∧ p ≤ p + x ∧ q ≤ z + q ∧ y + z ≤ x + y + (z + q) ∧
        x + y ≤ p + x + (y + z) := by
    intro p x y z q
    exact ⟨by ring, le_iff_exists_add.2 ⟨y, by ring⟩, le_iff_exists_add.2 ⟨y, by ring⟩,
      le_iff_exists_add.2 ⟨x, by ring⟩, le_iff_exists_add.2 ⟨z, by ring⟩,
      le_iff_exists_add.2 ⟨x + q, by ring⟩, le_iff_exists_add.2 ⟨p + z, by ring⟩⟩
  unfold invLen coinvLen
  rw [L1, L2, L3, L4, r1, r4]
  exact arith _ _ _ _ _
