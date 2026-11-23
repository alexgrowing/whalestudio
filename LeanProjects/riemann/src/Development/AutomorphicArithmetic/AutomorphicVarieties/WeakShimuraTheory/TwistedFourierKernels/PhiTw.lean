import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.H5.phiTw :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (β₀ : K.V.frame.G₀ →* c'.Oˣ), β₀.comp K.V.pr = K.β → ∀ (n : ℕ) (φ φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ → K.IsPhi X n B φ' → TwMap B (φ : B.B →+* X.B) (φ' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) (β₀ ^ n)) := by
  intro Ω _ _ _ l _ c D T c' h K X B β₀ hb n φ φ' hφ hφ'
  have hβ₀ : ∀ x, β₀ (K.V.pr x) = K.β x := fun x => DFunLike.congr_fun hb x
  rcases subsingleton_or_nontrivial X.B with hs | hs
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  haveI : Nontrivial X.A := ⟨⟨0, 1, fun h0 => zero_ne_one (X.inj (by simpa using h0))⟩⟩
  have hd : ∀ y, (X.cp y).natDegree = 4 := fun y => by
    rw [← natDegree_map_eq_of_injective X.inj, X.cp_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsurj : Function.Surjective K.V.pr := (prFacts K.V).1.surjective
  have hp : ∀ x, ((W.pushCh (algebraMap c'.O X.B) (β₀ ^ n)) x : X.B) = (algebraMap c'.O X.B (β₀ x : c'.O)) ^ n := by
    intro x
    simp [W.pushCh]
  constructor
  · intro g i hi
    obtain ⟨x, rfl⟩ := hsurj g
    have e0 := hφ.1 x
    have e1 := hφ'.1 x
    simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one]
    rw [← coeff_map, ← coeff_map, e0, e1, coeff_scaleRoots, coeff_scaleRoots, hd, Nat.sub_sub_self hi]
    erw [hp, hβ₀]
    simp only [pow_zero, mul_one, map_mul, map_pow]
    ring
  · intro v i g
    obtain ⟨g, hg⟩ := g
    have e0 := hφ.2 v i ⟨g, hg⟩
    have e1 := hφ'.2 v i ⟨g, hg⟩
    erw [e0, e1, hp]
    have hv : β₀ (K.V.pr g) = K.β g := hβ₀ g
    erw [hv]
    simp only [pow_zero, mul_one, map_mul, map_pow]
    ring
