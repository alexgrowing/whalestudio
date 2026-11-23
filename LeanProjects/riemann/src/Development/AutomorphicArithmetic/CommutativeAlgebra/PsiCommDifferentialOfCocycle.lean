import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

private theorem map_units {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (ε : ℤˣ) (x : Sec F U) :
    Sec.map φ (ε • x) = ε • Sec.map φ x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y :=
  map_add _ _ _

private theorem mul_mid {R : Type} [CommRing R] {I Q P : Cx R} (μ : Pair Q P I) (U : Scheme.{0}) (k m m' w : ℤ) (e : m = m')
    (h : m + 1 = w) (h' : m' + 1 = w) (A : Sec (Q.X k) U) (B : Sec (P.X 1) U) :
    μ.mul U m 1 w h (Sec.map (Q.d k m) A) B = μ.mul U m' 1 w h' (Sec.map (Q.d k m') A) B := by
  subst e
  rfl

theorem UpperTheory.psi_comm_differential_of_cocycle :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W), Sec.map (P.d 1 2) z = 0 →
        ∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec ((LL I Q).X s) T),
          Sec.map (I.d s t) (psi W μ z T s a) = psi W μ z T t (Sec.map ((LL I Q).d s t) a) := by
  intro R _ W I Q P μ z hz T s t a
  by_cases hst : s + 1 = t
  · subst hst
    have hB : Sec.map (P.d 1 (1 + 1)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z) = 0 := by
      rw [← res_map]
      have h2 : Sec.map (P.d 1 (1 + 1)) z = 0 := hz
      rw [h2]
      exact map_zero _
    have hL := μ.leibniz (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a))
      (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [hB, map_zero, smul_zero, add_zero,
      mul_mid μ (W ⨯ T) (s + -1) (s + -1 + 1) (s + 1 + -1) (s + 1) (by omega) (by omega) (by omega)] at hL
    change Sec.map (I.d s (s + 1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
        s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
      Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (Sec.map ((LL I Q).d s (s + 1)) a)) +
        (s + 1).negOnePow • μ.mul (W ⨯ T) (s + 1 + -1) 1 (s + 1) (by omega)
          (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (Sec.map ((LL I Q).d s (s + 1)) a))) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [map_add', map_units, hL, c₁_d, c₂_d, res_map, Int.negOnePow_succ]
    congr 1
    have hn : Sec.res (prod.snd : W ⨯ T ⟶ T) (- Sec.map (Q.d (s + -1) (s + 1 + -1)) (c₂ a)) =
        - Sec.map (Q.d (s + -1) (s + 1 + -1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) := by
      rw [← res_map]
      exact map_neg _ _
    rw [hn, map_neg, LinearMap.neg_apply, smul_neg, Units.neg_smul, neg_neg]
  · have h1 : I.d s t = 0 := I.shape _ _ hst
    have h2 : (LL I Q).d s t = 0 := (LL I Q).shape _ _ hst
    rw [h1, h2, map_zeroS, map_zeroS, map_zero]
