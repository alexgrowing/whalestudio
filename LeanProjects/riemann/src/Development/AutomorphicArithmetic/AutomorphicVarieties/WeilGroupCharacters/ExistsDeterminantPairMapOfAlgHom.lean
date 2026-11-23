import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

variable {n : ℕ} {A A' A'' G : Type} [CommRing A] [CommRing A'] [CommRing A''] [Group G]

private theorem pm_map_map (D : GDet n A G) (f : A →+* A') (g : A' →+* A'') :
    (D.map f).map g = D.map (g.comp f) := rfl

private theorem pm_chi_map (D : GDet n A G) (f : A →+* A') (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  have h := D.nat A[X] A'[X]
    { (Polynomial.mapRingHom f : A[X] →+* A'[X]) with
      commutes' := fun a => by
        show Polynomial.map f (C a) = C (f a)
        simp }
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  show D.D A'[X] _ = D.D A'[X] (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp

private theorem pm_lam_map (D : GDet n A G) (f : A →+* A') (i : ℕ) (y : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
  simp [GDet.lam, pm_chi_map]

private theorem pm_lam_single (D : GDet n A G) (f : A →+* A') (i : ℕ) (g : G) :
    (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  rw [← pm_lam_map]; simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_determinantPair_map_of_algHom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (p : Pair r R), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ n r R _ _ _ R' _ _ _ f p
  have hle : ∀ N, maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  have heps : ∀ g, Units.map ((f : R →+* R') : R →* R') (F.eps O R g) = F.eps O R' g := fun g =>
    Units.ext (f.commutes _)
  refine ⟨
    { D := p.D.map (f : R →+* R')
      ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i)
      cont := fun i N => ?_
      red := ?_
      psi := fun v i =>
        { cont := fun N => ((p.psi v i).cont N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
          red := fun g => (res_map f _).trans ((p.psi v i).red g)
          mu := fun g => (congrArg f ((p.psi v i).mu g)).trans (f.commutes _) }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pm_lam_single]
    exact (p.cont i N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
  · rw [pm_map_map, ← p.red]
    congr 1
    exact RingHom.ext (res_map f)
  · have h1 : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op, MonoidAlgebra.mapRingHom_single]
      rw [← heps, ← map_zpow]
      rfl
    rw [h1, pm_lam_map, p.P, pm_lam_single]
  · have h1 : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      simp only [GFrame.oEl, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
        MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.Ord v g h)).trans (map_zero _)
  · have h1 : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single g 1 - 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      simp only [map_mul, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.I u g hg h)).trans (map_zero _)
