import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.RepChi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_point {A B K : Type} [CommRing A] [CommRing B] [Field K] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* K) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (M.map y).charpoly.scaleRoots (y (i b)) := by
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.Pu.ptCp :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ρ : G T.L Ω →* GL (Fin 4) (PadicAlgCl l)), K.IsPhi X 0 B φ → (Link.pt φ y).IsRep ρ →
      ∀ g, (W.mat ρ g).charpoly = ((X.P.map (y : X.A →+* PadicAlgCl l)).r (resLe T.F_le g)).charpoly.scaleRoots (K.kapQ g : PadicAlgCl l) := by
  intro Ω _ _ _ l _ c D T c' h K X B φ y ρ hφ hρ g
  have hxe : (Link.pt φ y : B.B →+* PadicAlgCl l) =
      ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B) :=
    RingHom.ext fun b => Link.pt_apply K φ y b
  have hs : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B (K.κ g * K.β g ^ 0))) =
      (K.kapQ g : PadicAlgCl l) := by
    rw [← IsScalarTower.algebraMap_apply, pow_zero, mul_one]
    exact y.commutes _
  rw [UpperTheory.V.Ws.Pu.repChi K.V B _ ρ hρ g, hxe, ← Polynomial.map_map]
  refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
  rw [scale_point _ X.inj _ _ _ (X.cp_map _), hs]
  rfl
