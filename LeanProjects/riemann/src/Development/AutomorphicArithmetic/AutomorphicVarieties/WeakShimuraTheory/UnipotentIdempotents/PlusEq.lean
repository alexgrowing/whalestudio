import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem plus_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (x : Ω) : x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x := by
  classical
  set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef
  let e : E ≃+* T.F :=
    { toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩
      invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm
  have hEM : E ≤ maximalRealSubfield T.L := IsTotallyReal.le_maximalRealSubfield E
  have hdE : Module.finrank ℚ E = Module.finrank ℚ T.F :=
    (RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq
  have hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2 := by
    have h1 := IntermediateField.finrank_sup_le T.F T.K
    rw [T.degK, ← T.hL] at h1
    exact h1
  have hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]
    exact Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L
  have hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L :=
    Module.finrank_mul_finrank ℚ E T.L
  have hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L) := Module.finrank_pos
  have hdeg : Module.finrank E T.L = 2 := by
    apply le_antisymm
    · have : Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2 := by
        rw [hE2, hdE]; exact hsup
      exact Nat.le_of_mul_le_mul_left this hpos
    · have : Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤
          Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L := by
        rw [hM, ← hE2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left this hposM
  haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }
  have hEq : E = maximalRealSubfield T.L := NumberField.CMExtension.eq_maximalRealSubfield T.L E
  constructor
  · intro hx
    have hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L := by
      rw [← hEq]; exact hx
    exact ⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : T.L) ∈ E := by rw [hEq]; exact y.2
    exact hy

private theorem fix_L {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (τ : G T.F Ω) : τ ∈ T.GalL ↔ ∀ x : T.L, τ (x : Ω) = x := by
  have hF : resQ T.F τ ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  unfold Tower.GalL
  rw [Subgroup.mem_comap]
  constructor
  · intro h x
    have hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, h⟩
    rw [← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hsup
    exact hsup x x.2
  · intro h
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact h ⟨y, Lk.K_le T hy⟩

theorem UpperTheory.V.Ws.Lk.galEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), (∀ x : Ω, x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x) ∧ (∃ φ : G (W.Lp T.L) Ω ≃* G T.F Ω, (∀ σ x, φ σ x = σ x) ∧ ∀ σ, φ σ ∈ T.GalL ↔ σ ∈ (W.resP T.L Ω).range) ∧ ∀ τ : G T.F Ω, τ ∈ T.GalL ↔ τ ∈ (resLe T.F_le).range := by
  intro Ω _ _ _ l _ c D T
  have hP := plus_eq T
  refine ⟨hP, ?_, ?_⟩
  · let φ : G (W.Lp T.L) Ω ≃* G T.F Ω :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by
            obtain ⟨y, hy⟩ := (hP (x : Ω)).1 x.2
            change σ (x : Ω) = (x : Ω)
            rw [← hy]
            exact σ.commutes y)
        invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by
            have hx := (hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
            exact σ.commutes ⟨_, hx⟩)
        left_inv := fun σ => by ext; rfl
        right_inv := fun σ => by ext; rfl
        map_mul' := fun σ τ => by ext; rfl }
    refine ⟨φ, fun σ x => rfl, fun σ => ?_⟩
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
  · intro τ
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
