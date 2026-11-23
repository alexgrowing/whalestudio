import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Pu.arith :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l), D.Good → K.IsPhi X 0 B φ →
      T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) → ∃ w : K.s.Wt 4, (Link.pt φ y).Arith w := by
  intro hA Ω _ _ _ l _ c D T c' h K X B φ y hD hφ hW
  have he := hD.two_le
  refine auArith hA D T c' h K X B φ hφ y (Link.pt φ y) (fun b => rfl) (fun v i => Pt.psi_cont _ v i)
    (fun i => (D.wts4 i : ℤ)) ?_ hW
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> simp [Raw.wts4] <;> omega
