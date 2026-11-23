import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.P1.psPair_fac {Λ B k : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    [Field k] [Algebra Λ k] (φ : B →+* k) (h1 : ∀ a, φ (algebraMap Λ B a) = algebraMap Λ k a)
    (h2 : ∀ b ∈ maximalIdeal B, φ b = 0) :
    ∃ j : ResidueField Λ →+* k, (∀ a, j (residue Λ a) = algebraMap Λ k a) ∧ ∀ b, j (res Λ B b) = φ b := by
  have h3 : ∀ a ∈ maximalIdeal Λ, algebraMap Λ k a = 0 := fun a ha => by
    rw [← h1]
    exact h2 _ fun hu => ha (IsLocalHom.map_nonunit a hu)
  refine ⟨Ideal.Quotient.lift _ (algebraMap Λ k) h3, fun a => rfl, fun b => ?_⟩
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) b
  have e1 : res Λ B b = residue Λ a := by
    have := (res_eq_zero_iff Λ B _).2 ha
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have e2 := h2 _ ha
  rw [map_sub, sub_eq_zero, h1] at e2
  rw [e1, e2]
  rfl

private theorem UpperTheory.V.Ws.P1.psPair_cont {Γ A R : Type} [TopologicalSpace Γ] [CommRing A] [CommRing R] (f : A →+* R)
    {I : Ideal A} {J : Ideal R} (hI : I.map f ≤ J) {u : Γ → A} (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI N
  exact (hu N).comp (Ideal.quotientMap (J ^ N) f hN)

theorem UpperTheory.V.Ws.P1.psPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (k : Type) [Field k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
          (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) → T.PsPair h k (X.P.map (y : X.A →+* PowerSeries k)) := by
  intro Ω _ _ _ l _ c D T c' h X k _ _ y hy
  let φ : X.B →+* k := ((PowerSeries.constantCoeff : PowerSeries k →+* k).comp (y : X.A →+* PowerSeries k)).comp (algebraMap X.B X.A)
  have hφ : ∀ b, φ b = PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) := fun b => rfl
  have h1 : ∀ a, φ (algebraMap c'.O X.B a) = algebraMap c'.O k a := fun a => by
    rw [hφ, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C]
  obtain ⟨j, hj1, hj2⟩ := UpperTheory.V.Ws.P1.psPair_fac φ h1 hy
  obtain ⟨hψ, hp, -⟩ := sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P
  refine ⟨fun a ha => ?_, ?_, fun i i' => ?_, fun g => ?_, fun v i s hs => ?_⟩
  · rw [← hj1, (residue_eq_zero_iff a).2 ha, map_zero]
  · have := hp X.pair
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at this
  · refine UpperTheory.V.Ws.P1.psPair_cont (y : X.A →+* PowerSeries k) ?_ (X.cont i i')
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    have := hy b hb
    intro hu
    exact hu.ne_zero this
  · have e : (X.P.map (y : X.A →+* PowerSeries k)).r g = (X.P.r g).map (y : X.A →+* PowerSeries k) := rfl
    have e2 : φ = j.comp (res c'.O X.B : X.B →+* ResidueField c'.O) := RingHom.ext fun b => (hj2 b).symm
    rw [e, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map, Polynomial.map_map]
    show (X.cp g).map φ = _
    rw [e2, ← Polynomial.map_map, X.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj1]
    rfl
  · have e1 := hψ v i s
    rw [← X.ψ_map v i s hs] at e1
    have e2 := hj2 (X.ψ v i s)
    rw [X.ψ_red v i s hs, hj1] at e2
    exact (congrArg PowerSeries.constantCoeff e1).trans e2.symm
