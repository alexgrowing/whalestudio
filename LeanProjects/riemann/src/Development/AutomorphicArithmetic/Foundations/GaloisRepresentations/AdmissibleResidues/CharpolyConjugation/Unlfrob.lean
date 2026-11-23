import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.UnlAway
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma root_inv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) {n : ℕ} (g : GL (Fin n) K) (y : L)
    (h : ((g : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y) :
    y ≠ 0 ∧ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y⁻¹ := by
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x :=
    (Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective).1 h
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  refine ⟨by simpa using hx0, ?_⟩
  have := (Polynomial.isRoot_map_iff (f := e.toRingHom) (x := x⁻¹) e.injective).2
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi)
  simpa using this

theorem UpperTheory.GalN.V.L.unlfrob :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (S : Multiset ℂ), IsPlaceOver A w → FrobEig ι r w S → (∀ α ∈ S, ∀ β ∈ S, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖) → UnlAt ι r w A := by
  intro F Ω _ _ _ _ _ l _ ι n r w A S hA hS hlt
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α hα hqα
  have hP := (hS A hA).2 s hs
  have key : ∀ y : ℂ, ((r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot y →
      y ≠ 0 ∧ y⁻¹ ∈ S := by
    intro y hy
    obtain ⟨hy0, hr⟩ := root_inv ι (r s) y hy
    refine ⟨hy0, ?_⟩
    have hroots : (((r s⁻¹ : Matrix (Fin n) (Fin n) (Qbar l))).charpoly.map ι.toRingHom).roots = S := by
      rw [hP]; exact Polynomial.roots_multiset_prod_X_sub_C S
    rw [← hroots, Polynomial.mem_roots ((Matrix.charpoly_monic _).map _).ne_zero, map_inv]
    exact hr
  obtain ⟨ha0, ha⟩ := key α hα
  obtain ⟨hb0, hb⟩ := key _ hqα
  have hq0 : (((normV w : ℕ) : ℂ)) ≠ 0 := by
    intro h0
    apply hb0
    simp [h0]
  have hlt' := hlt _ ha _ hb
  have hqr : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have : (normV w : ℕ) ≠ 0 := by exact_mod_cast hq0
    exact_mod_cast Nat.pos_of_ne_zero this
  have heq : ((normV w : ℕ) : ℝ) * ‖((((normV w : ℕ) : ℂ) ^ 1 * α))⁻¹‖ = ‖α⁻¹‖ := by
    rw [pow_one, norm_inv, norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
    field_simp
  exact absurd hlt' (by rw [heq]; exact lt_irrefl _)
