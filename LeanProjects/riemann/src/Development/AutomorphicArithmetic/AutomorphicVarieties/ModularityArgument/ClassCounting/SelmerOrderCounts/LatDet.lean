import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.latDet :
    ∀ (E V : Type) [AddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (lam : E →ₗ[ℤ] V) (δ : Module.End ℤ E) (δV : V →ₗ[ℝ] V), (∀ x, lam (δ x) = δV (lam x)) → LinearMap.ker lam = Submodule.torsion ℤ E → DiscreteTopology (LinearMap.range lam) → Submodule.span ℝ (LinearMap.range lam : Set V) = ⊤ → LinearMap.det δV ≠ 0 → Finite (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ∧ (Nat.card (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) : ℝ) = |LinearMap.det δV| := by
  intro E V _ _ _ _ lam δ δV hcomm hker hdisc hspan hdet
  classical
  set L := LinearMap.range lam with hL
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  have hmaps : ∀ x ∈ L, (δV.restrictScalars ℤ) x ∈ L := by
    rintro _ ⟨y, rfl⟩
    exact ⟨δ y, by simp [hcomm]⟩
  set f : L →ₗ[ℤ] L := (δV.restrictScalars ℤ).restrict hmaps with hf
  have hfv : ∀ y : L, ((f y : L) : V) = δV y := fun y => rfl
  have hVinj : Function.Injective δV := fun a b h =>
    (LinearMap.equivOfDetNeZero δV hdet).injective h
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hVinj
    rw [← hfv, ← hfv, h]
  have hcard : Nat.card (L ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
    rw [← Submodule.natAbs_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hfinj)]
    congr 2
  have hdetf : ((LinearMap.det f : ℤ) : ℝ) = LinearMap.det δV := by
    let b := Module.Free.chooseBasis ℤ L
    let bV := b.ofZLatticeBasis ℝ L
    have hM : (Int.castRingHom ℝ).mapMatrix (LinearMap.toMatrix b b f) =
        LinearMap.toMatrix bV bV δV := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, eq_intCast]
      rw [show bV j = ((b j : L) : V) from b.ofZLatticeBasis_apply ℝ L j, ← hfv,
        Module.Basis.ofZLatticeBasis_repr_apply]
    rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bV, ← hM, ← RingHom.map_det,
      eq_intCast]
  have hne : (LinearMap.det f).natAbs ≠ 0 := by
    intro h
    apply hdet
    rw [← hdetf, Int.natAbs_eq_zero.mp h, Int.cast_zero]
  let g : E →ₗ[ℤ] L ⧸ LinearMap.range f := (LinearMap.range f).mkQ ∘ₗ lam.rangeRestrict
  have hgs : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp lam.surjective_rangeRestrict
  have hkerg : LinearMap.ker g = LinearMap.range δ ⊔ Submodule.torsion ℤ E := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_sup, LinearMap.mem_range]
    constructor
    · rintro ⟨⟨_, z, rfl⟩, hz⟩
      refine ⟨δ z, ⟨z, rfl⟩, x - δ z, ?_, by abel⟩
      rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have := congrArg Subtype.val hz
      rw [hfv] at this
      simpa [hcomm] using this.symm
    · rintro ⟨_, ⟨z, rfl⟩, t, ht, rfl⟩
      rw [← hker, LinearMap.mem_ker] at ht
      refine ⟨lam.rangeRestrict z, Subtype.ext ?_⟩
      rw [hfv]
      simp [hcomm, ht]
  let e2 : (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ≃ₗ[ℤ] L ⧸ LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hkerg.symm).trans (g.quotKerEquivOfSurjective hgs)
  haveI : Finite (L ⧸ LinearMap.range f) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  refine ⟨Finite.of_equiv _ e2.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e2.toEquiv, hcard, Nat.cast_natAbs, Int.cast_abs, hdetf]
