import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitarStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.DefiniteBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem satLink_of (P : Hypotheses₂) : SatLink := by
  intro E _ _ _ a π
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem algSat_inj {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) {B B' : Multiset ℂˣ}
    (h : ((algSat n (normV w) B).map fun b => X - C b).prod = ((algSat n (normV w) B').map fun b => X - C b).prod) :
    B = B' := by
  have h3 := congrArg Polynomial.roots h
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have h4 := Multiset.map_injective
    (mul_right_injective₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq (((n : ℝ) - 1) / 2)).ne')) (a₁ := B.map Units.val)
    (a₂ := B'.map Units.val) (by simpa [algSat, Multiset.map_map] using h3)
  exact Multiset.map_injective Units.val_injective h4

private theorem eq_of_split {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} [IsCMField L]
    (hE : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal)
    (r : G L Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (f : G L Ω → (Qbar l)[X])
    (hf : ∀ j, Continuous fun g => (f g).coeff j)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, IsSplitAt w → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ σ : G L Ω, IsFrob A (normV w) σ → (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f σ) (g : G L Ω) :
    (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f g := by
  have contCoeff : ∀ i : ℕ, Continuous fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i := fun i => by
    have h : (fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i) =
        fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ (Qbar l) (Fin n)).coeff i) := by
      funext M
      exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id _) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  ext i
  have h1 : Continuous fun g : G L Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (contCoeff i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
  refine congrFun (Continuous.ext_on hD h1 (hf i) ?_) g
  rintro σ ⟨v, hv, hd, A, hA, hσ⟩
  have h := not_not.1 hv (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hE v) hd) A hA σ hσ
  simp only [h]

private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]

private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
