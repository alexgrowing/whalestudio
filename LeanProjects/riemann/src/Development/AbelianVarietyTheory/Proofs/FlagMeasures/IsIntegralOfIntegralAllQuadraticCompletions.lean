import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GlueInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem nonempty_place' : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem nontrivial_Ep (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) : Nontrivial (A.loc p).Ep :=
  Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := nonempty_place' (F := F)
  haveI := nontrivial_Ep A p
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem sig_ne_id (A : Places F E sig) : ¬ ∀ y, sig y = y := by
  intro h
  obtain ⟨p⟩ := nonempty_place' (F := F)
  have hcj : (A.L p).cj.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range (A.loc p).span fun y => by
      simp [A.L_cj, (A.loc p).cj_ιE, h]
  have hall : ∀ z : (A.loc p).Ep, ∃ c : (A.loc p).Fp, c • (1 : (A.loc p).Ep) = z := fun z => by
    obtain ⟨a, ha⟩ := ((A.L p).cj_fix z).1 (by simpa using LinearMap.congr_fun hcj z)
    exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  have := finrank_le_one (1 : (A.loc p).Ep) hall
  rw [(A.loc p).rank] at this
  norm_num at this

theorem fix_mem (A : Places F E sig) (s : E) (hs : sig s = s) : ∃ t : F, algebraMap F E t = s := by
  by_contra hno
  push_neg at hno
  apply sig_ne_id A
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
      have hab' : algebraMap F E a + algebraMap F E b * s = 0 := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab; exact hab
      apply hno (-a / b)
      rw [map_div₀, map_neg, div_eq_iff hb']
      linear_combination (-1 : E) * hab'
  have hspan : Submodule.span F (Set.range ![(1 : E), s]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, A.quad]
    simp
  have hid : sig.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range hspan fun i => by
      fin_cases i <;> simp [hs]
  exact fun y => LinearMap.congr_fun hid y

theorem int_of_loc (A : Places F E sig) (t : F)
    (h : ∀ p, (A.loc p).ιE (algebraMap F E t) ∈ (A.L p).O) : t ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro p
  haveI := nontrivial_Ep A p
  have h1 := h p
  rw [(A.loc p).compat, (A.L p).O_def] at h1
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] ((A.loc p).ιF t) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h1
  have h3 := (Valuation.integer.integers (valuation (A.loc p).Fp)).mem_of_integral h2
  have h4 : (A.loc p).ιF t ≤ᵥ (A.loc p).ιF 1 := by
    rw [map_one]
    exact (Valuation.Compatible.vle_iff_le (v := valuation (A.loc p).Fp) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 h3)
  simpa using ((A.loc p).val t 1).1 h4

theorem sig_mem (A : Places F E sig) (y : E) (p : HeightOneSpectrum (𝓞 F))
    (hy : (A.loc p).ιE y ∈ (A.L p).O) : (A.loc p).ιE (sig y) ∈ (A.L p).O := by
  rw [← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).O_def]
  exact (((A.L p).O_def _).1 hy).map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

theorem isIntegral_of_quadratic (y a b : E) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (h : y ^ 2 - a * y + b = 0) : IsIntegral ℤ y := by
  have hR : IsIntegral (integralClosure ℤ E) y := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, ha⟩ : integralClosure ℤ E) * Polynomial.X +
      Polynomial.C (⟨b, hb⟩ : integralClosure ℤ E), by monicity!, ?_⟩
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul] using h
  exact isIntegral_trans y hR

end GlobalTheory.HL.GlueInt

open GlobalTheory.HL.GlueInt in

theorem GlobalTheory.HL.isIntegral_of_forall_mem_O : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) →
    IsIntegral ℤ y := by
  intro F E _ _ _ _ _ sig A y hy
  obtain ⟨a, ha⟩ := fix_mem A (y + sig y) (by rw [map_add, sig_sig A, add_comm])
  obtain ⟨b, hb⟩ := fix_mem A (y * sig y) (by rw [map_mul, sig_sig A, mul_comm])
  obtain ⟨a0, rfl⟩ := int_of_loc A a fun p => by
    rw [ha, map_add]; exact (A.L p).O.add_mem (hy p) (sig_mem A y p (hy p))
  obtain ⟨b0, rfl⟩ := int_of_loc A b fun p => by
    rw [hb, map_mul]; exact (A.L p).O.mul_mem (hy p) (sig_mem A y p (hy p))
  refine isIntegral_of_quadratic y _ _ ((RingOfIntegers.isIntegral_coe a0).map (algebraMap F E).toIntAlgHom)
    ((RingOfIntegers.isIntegral_coe b0).map (algebraMap F E).toIntAlgHom) ?_
  change y ^ 2 - algebraMap F E (algebraMap (𝓞 F) F a0) * y + algebraMap F E (algebraMap (𝓞 F) F b0) = 0
  rw [ha, hb]
  ring
