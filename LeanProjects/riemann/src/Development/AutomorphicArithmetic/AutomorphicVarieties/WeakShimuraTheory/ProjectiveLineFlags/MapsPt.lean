import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.DetExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CpSmul

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_pt {A B R : Type} [CommRing A] [CommRing B] [CommRing R] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* R) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (y (i b) • M.map y).charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), (UpperTheory.V.Ws.P1.cpSmul _ _).1, ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.P1.mapsPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ →
          ∀ (R : Type) [CommRing R] [Algebra c'.O R] (y : X.A →ₐ[c'.O] R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ),
          K.IsRho ρ (X.P.map (y : X.A →+* R)) → K.IsPsi ψ (X.P.map (y : X.A →+* R)) →
          B.u.Maps (((y : X.A →+* R).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B)) (W.GDet.ofRep (W.mat ρ)) ψ := by
  intro Ω _ _ _ l _ c D T c' h K X B φ hφ R _ _ y ρ ψ hρ hψ
  have hs : ∀ a : c'.O, (y : X.A →+* R) (algebraMap X.B X.A (algebraMap c'.O X.B a)) = algebraMap c'.O R a := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    exact y.commutes a
  refine ⟨UpperTheory.V.Ws.P1.detExt _ _ _ fun g0 => ?_, fun v i => ?_⟩
  · obtain ⟨g, rfl⟩ := (UpperTheory.V.Ws.phiKer K.V).1 g0
    refine Eq.trans ?_ ((AlgebraTools.Det.repApi _).2.1 _).symm
    rw [← Polynomial.map_map]
    refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
    rw [scale_pt _ X.inj _ _ _ (X.cp_map _), hs, pow_zero, mul_one]
    exact congrArg Matrix.charpoly (hρ g).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    have hd0 : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) := by
      intro v g
      rw [← K.hA v]; exact g.2
    have hd := hd0 v g
    refine Eq.trans ?_ (hψ v i g).symm
    refine (congrArg (fun b => (y : X.A →+* R) (algebraMap X.B X.A b)) (hφ.2 v i g)).trans ?_
    simp only [pow_zero, mul_one]
    rw [map_mul, map_mul, hs, X.ψ_map _ _ _ hd]
    exact congrArg _ ((UpperTheory.V.Ws.sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* R) X.P).1 _ _ _).symm
