import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem chi_ofRep' {n : ℕ} {A Γ : Type} [CommRing A] [Group Γ] (ρ : Γ →* Matrix (Fin n) (Fin n) A) (g : Γ) :
    (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  simp only [W.GDet.chi, W.GDet.ofRep, W.GDet.repAlg, MonoidHom.coe_comp, Function.comp_apply,
    map_sub, MonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, MonoidAlgebra.lift_single, Matrix.coe_detMonoidHom, map_one]
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.sub_apply]

private theorem chi_comap' {n : ℕ} {A Γ H : Type} [CommRing A] [Group Γ] [Group H] (D : W.GDet n A Γ) (φ : H →* Γ) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem chi_map' {n : ℕ} {A A' Γ : Type} [CommRing A] [CommRing A'] [Group Γ] (D : W.GDet n A Γ) (f : A →+* A') (g : Γ) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] A'[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have h := D.nat A[X] A'[X] φ
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1))
  have e : (MonoidAlgebra.mapRingHom Γ (φ : A[X] →+* A'[X]))
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1)) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom Γ C (MonoidAlgebra.single g 1) := by
    simp [φ, MonoidAlgebra.mapRingHom_single]
  rw [e] at h
  exact h

theorem UpperTheory.V.Ws.Pu.repChi :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → ∀ g, (W.mat ρ g).charpoly = (B.u.D.chi (MonoidAlgebra.single (V.pr g) 1)).map (x : B.B →+* PadicAlgCl l) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx g
  refine (chi_ofRep' (W.mat ρ) g).symm.trans ?_
  refine (congrArg (fun D => W.GDet.chi D (MonoidAlgebra.single g 1)) hx.symm).trans ?_
  exact (chi_comap' x.D V.pr g).trans (chi_map' B.u.D _ _)
