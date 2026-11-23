import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.QbarInst

attribute [local instance] UpperTheory.V.QbarInst.charZero UpperTheory.V.QbarInst.torsionFree UpperTheory.V.QbarInst.algClosure

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd

noncomputable section

namespace UpperTheory.V.Br.CharacterEquality

private theorem normV_inj : Function.Injective fun w : Pl ℚ => normV w := fun v w h =>
  HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])

private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : Pl ℚ, normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : Pl ℚ := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

private theorem tr_det {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.trace = a ∧ ι A.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (Polynomial.coeff · 0) h
  have h1 := congrArg (Polynomial.coeff · 1) h
  simp at h0 h1
  exact ⟨h1, h0⟩

private theorem two_det {K : Type} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    2 * A.det = A.trace ^ 2 - (A * A).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem exists_rep (P : HypothesesH) (ι : Qbar 2 ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 2 ≤ k) {χ : DirichletCharacter ℂ N}
    (g : Eigenform k N χ) : ∃ r : G ℚ (AlgebraicClosure ℚ) →* GL (Fin 2) (Qbar 2), Continuous r ∧
      ∀ᶠ w : Pl ℚ in Filter.cofinite, ∀ A : ValuationSubring (AlgebraicClosure ℚ), IsPlaceOver A w →
        ∀ σ : G ℚ (AlgebraicClosure ℚ), IsFrob A (normV w) σ →
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace = g.a (normV w) ∧
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det = χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) := by
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N hk χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, -, -, hsat⟩ := holRep P ℚ k hk _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := exR P ℚ (AlgebraicClosure ℚ) 2 ι 2 one_le_two π χ' hreg hpol
  refine ⟨r, hG.cont, ?_⟩
  filter_upwards [hatt.2, normV_inj.tendsto_cofinite.eventually (Set.finite_le_nat N).eventually_cofinite_notMem]
    with w ⟨B₁, hB₁, hF⟩ hw A hA σ hσ
  have hq : ¬ normV w ∣ N := fun h => hw (Nat.le_of_dvd (NeZero.pos N) h)
  obtain ⟨B₂, hB₂, e⟩ := hsat w (Nat.factorization_eq_zero_of_not_dvd hq)
  obtain rfl := hB₁.unique hB₂
  rw [← (hval w hq).2]
  exact tr_det ι (((hF A hA).2 σ hσ).trans e)

end UpperTheory.V.Br.CharacterEquality
