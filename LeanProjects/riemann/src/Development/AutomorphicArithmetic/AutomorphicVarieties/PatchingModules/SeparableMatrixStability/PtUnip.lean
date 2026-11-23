import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.UnipOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_ofRep_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem kills_max {B K : Type} [CommRing B] [IsLocalRing B] [Field K] [Finite K] (g : B →+* K) (b : B)
    (hb : b ∈ maximalIdeal B) : g b = 0 := by
  by_contra h
  haveI := Fintype.ofFinite K
  have h1 := FiniteField.pow_card_sub_one_eq_one (g b) h
  have h2 : Fintype.card K - 1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  have h3 : IsUnit (1 - b ^ (Fintype.card K - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero h2))
  have h4 := h3.map g
  rw [map_sub, map_one, map_pow, h1, sub_self] at h4
  exact not_isUnit_zero h4

theorem UpperTheory.V.Pa.pt_unip :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → P.x.UnipOn T.H.toSubgroup := by
  intro l _ L G0 T n O _ _ _ r B _ _ _ u D0 P hA
  refine UpperTheory.V.Pa.unip_of l G0.frame n P.x _ fun h hh => ?_
  have key : ∀ {C : Type} [CommRing C] (f : B →+* C), (u.D.map f).chi (MonoidAlgebra.single h 1) =
      (u.D.chi (MonoidAlgebra.single h 1)).map f := fun f => by
    have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 f (MonoidAlgebra.single h 1)).1
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  have h1 := key P.f.toRingHom
  rw [P.maps.1, chi_ofRep_single] at h1
  have h2 := key (res O B : B →+* ResidueField O)
  rw [u.red, Resid.Dbar, chi_ofRep_single] at h2
  have h3 : (UpperTheory.V.W.diagRep r.chib) h = 1 := by
    change Matrix.diagonal (fun i => ((r.chib i h : (ResidueField O)ˣ) : ResidueField O)) = 1
    simp [hA.1 h hh]
  rw [h3, Matrix.charpoly_one, Fintype.card_fin] at h2
  have h4 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map (res O B : B →+* ResidueField O) = 0 := by
    rw [Polynomial.map_sub, ← h2]
    simp
  have h5 : (u.D.chi (MonoidAlgebra.single h 1) - (Polynomial.X - 1) ^ n).map
      ((PowerSeries.constantCoeff : P.x.A →+* P.x.K).comp P.f.toRingHom) = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    refine kills_max _ _ ((res_eq_zero_iff O B _).1 ?_)
    have := congrArg (fun p => Polynomial.coeff p k) h4
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_coe] using this
  rw [Polynomial.map_sub, sub_eq_zero] at h5
  rw [h1, Polynomial.map_map, h5]
  simp
