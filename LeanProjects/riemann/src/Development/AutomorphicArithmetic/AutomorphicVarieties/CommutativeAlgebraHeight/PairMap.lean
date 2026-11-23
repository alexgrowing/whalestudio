import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem UpperTheory.V.CA.pair_map :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (p : Pair r R) (f : R →ₐ[O] R'), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ _ _ _ _ n r R R' _ _ _ _ _ _ p f
  obtain ⟨-, hcomp, hlam, -⟩ := d_gmap p.D
  have hl : ∀ i y, (p.D.map (f : R →+* R')).lam i (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = f (p.D.lam i y) :=
    fun i y => (hlam (f : R →+* R') y).2 i
  have h1 : ∀ g : F.G₀, MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single g 1 := fun g => by rw [MonoidAlgebra.mapRingHom_single, map_one]
  refine ⟨{ D := p.D.map (f : R →+* R'), ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i),
            cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, rfl, fun _ _ => rfl⟩
  · intro i
    have := adic_map f (p.cont i)
    simpa only [← hl, h1] using this
  · rw [hcomp, ← p.red]
    congr 1
    ext x
    exact res_map f x
  · intro v i
    refine ⟨adic_map f (p.psi v i).cont, fun g => (res_map f _).trans ((p.psi v i).red g), fun g => ?_⟩
    change f (p.ψ v i g : R) = _
    rw [(p.psi v i).mu g, f.commutes]
  · intro i g
    have hs : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      rw [star_single, star_single, MonoidAlgebra.mapRingHom_single]
      congr 1
      have he : F.eps O R' g = Units.map ((f : R →+* R') : R →* R') (F.eps O R g) :=
        Units.ext (f.commutes _).symm
      rw [he, ← map_zpow]
      rfl
    rw [hs, hl, p.P, ← hl, h1]
  · intro v g h
    have ho : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      rw [map_mul, h1, GFrame.oEl, GFrame.oEl, map_list_prod, List.map_ofFn]
      congr 3
      funext i
      simp only [Function.comp_apply, map_sub, h1, MonoidAlgebra.mapRingHom_single]
      rfl
    have := p.Ord v g h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
  · intro u g hg h
    have ho : (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1) : MonoidAlgebra R' F.G₀) =
        MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      rw [map_mul, map_sub, h1, h1, map_one]
    have := p.I u g hg h
    rw [GDet.tr] at this ⊢
    rw [ho, hl, this, map_zero]
