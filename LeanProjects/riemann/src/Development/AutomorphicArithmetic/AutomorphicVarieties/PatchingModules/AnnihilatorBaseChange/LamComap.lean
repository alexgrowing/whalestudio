import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  exact hy

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : ∀ x ∈ maximalIdeal R ^ N, Ideal.Quotient.mk (maximalIdeal R' ^ N) (f x) = 0 := by
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hm : maximalIdeal R ≤ Ideal.comap f (maximalIdeal R') := fun y hy => mem_map f hy
    exact Ideal.le_comap_pow f N (Ideal.pow_right_mono hm N hx)
  have hc := (ha N).comp (Ideal.Quotient.lift (maximalIdeal R ^ N)
    ((Ideal.Quotient.mk (maximalIdeal R' ^ N)).comp (f : R →+* R')) hle)
  convert hc using 1
  funext g
  rfl

private theorem map_X_mem {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] {σ : Type} [Finite σ] (f : MvPowerSeries σ R →ₐ[O] R') (a : σ) :
    f (MvPowerSeries.X a) ∈ maximalIdeal R' := by
  haveI : IsCO O (MvPowerSeries σ R) := co_mvps O R σ
  apply mem_map f
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp [MvPowerSeries.constantCoeff_X]

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply,
    MonoidAlgebra.mapRingHom_single, Polynomial.C_1]
  congr 4
  change MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1) = _
  rw [map_sub]
  simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

theorem UpperTheory.V.Pa.Core.tupPi :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) [IsCO O (Spo A)], ∃ t : Tup Λ A (Spo A), t.D = (u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A)) ∧ (t.ψ = fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i)) ∧ t.s = algebraMap B (Spo A) (A.b.lam (MvPowerSeries.X (.inl ()))) ∧ (t.U = fun j i => Sp.u _ _ j i) ∧ t.y = fun _ _ => 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A _
  let f : B →ₐ[O] Spo A := IsScalarTower.toAlgHom O B (Spo A)
  have hφc : Continuous (Λ.h.p₀.comp (πo0 Λ)) := (Λ.h.p₀_cont).comp Λ.πo0_cont
  refine ⟨⟨(u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A)), ?cont, ?red,
    fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i), ?psi,
    algebraMap B (Spo A) (A.b.lam (MvPowerSeries.X (.inl ()))), ?smem,
    fun j i => Sp.u _ _ j i, ?umem, fun _ _ => 0, fun _ _ => Ideal.zero_mem _⟩, rfl, rfl, rfl, rfl, rfl⟩
  case cont =>
    intro i
    have h1 : ∀ g, ((u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A))).lam i
        (MonoidAlgebra.single g 1) = f (u.D.lam i (MonoidAlgebra.single ((Λ.h.p₀.comp (πo0 Λ)) g) 1)) := by
      intro g
      have h2 := ((UpperTheory.V.CA.d_gmap (u.D.comap (Λ.h.p₀.comp (πo0 Λ)))).2.2.1 (algebraMap B (Spo A))
        (MonoidAlgebra.single g 1)).2 i
      rw [MonoidAlgebra.mapRingHom_single, map_one] at h2
      rw [h2, lam_comap]
      rfl
    simp only [h1]
    exact adic_map f (fun N => ((u.cont i) N).comp_continuous hφc)
  case red =>
    rw [(UpperTheory.V.CA.d_gmap _).2.1]
    have h3 : (↑(res O (Spo A)) : Spo A →+* ResidueField O).comp (algebraMap B (Spo A)) = ↑(res O B) :=
      RingHom.ext fun x => res_map f x
    rw [h3, ← u.red]
    rfl
  case psi =>
    intro v i
    refine ⟨adic_map f (u.psi v i).cont, fun g => ?_, fun g => ?_⟩
    · show res O (Spo A) (f ↑(u.ψ v i g)) = _
      rw [res_map]
      exact (u.psi v i).red g
    · show f ↑(u.ψ v i g) = _
      rw [(u.psi v i).mu g, AlgHom.commutes]
  case smem =>
    haveI : IsCO O O := IsCO.mk IsCoef.complete ⟨fun a ha => by simpa using ha⟩ (fun x => ⟨x, by simp⟩)
    exact _root_.mem_map f (map_X_mem A.b.lam (Sum.inl ()))
  case umem =>
    intro j i
    have hC : ∀ b : B, (MvPowerSeries.C b : MvPowerSeries (Fin T.q × Fin n) B) =
        algebraMap B (MvPowerSeries (Fin T.q × Fin n) B) b := fun b => by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h4 : Sp.u _ _ j i - algebraMap O (Spo A) (A.ut j i) =
        (Sp.mk _ _).restrictScalars O (MvPowerSeries.X (j, i)) := by
      simp only [Sp.u, map_add, AlgHom.restrictScalars_apply]
      rw [add_sub_right_comm, sub_eq_zero.mpr, zero_add]
      rw [hC, AlgHom.commutes, ← IsScalarTower.algebraMap_apply O B (Spo A)]
    rw [h4]
    exact map_X_mem _ (j, i)
