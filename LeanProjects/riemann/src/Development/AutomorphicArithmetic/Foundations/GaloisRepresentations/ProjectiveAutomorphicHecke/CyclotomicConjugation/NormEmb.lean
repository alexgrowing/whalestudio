import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

namespace UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings

private theorem eq_on_adjoin {E : Type} [Field E] [NumberField E] (x : E) (f g : E →+* ℂ)
    (h : f x = g x) (y : E) (hy : y ∈ IntermediateField.adjoin ℚ {x}) : f y = g y := by
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | inv a _ ha => simp [ha]
  | mul a b _ _ ha hb => simp [ha, hb]

private theorem norm_Kx {E : Type} [Field E] [NumberField E] (x : E) (φ : E →+* ℂ) (k : E)
    [DecidablePred fun φ' : E →+* ℂ => φ' x = φ x] :
    φ (algebraMap (Kx x) E (Algebra.norm (Kx x) k)) =
      ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = φ x), φ' k := by
  letI : Algebra (Kx x) ℂ := (φ.comp (algebraMap (Kx x) E)).toAlgebra
  haveI : FiniteDimensional (Kx x) E := FiniteDimensional.right ℚ (Kx x) E
  have hc : ∀ r : Kx x, algebraMap (Kx x) ℂ r = φ (algebraMap (Kx x) E r) := fun _ => rfl
  have h := Algebra.norm_eq_prod_embeddings (Kx x) ℂ k
  rw [hc] at h
  rw [h]
  refine Finset.prod_bij (fun σ _ => (σ : E →+* ℂ)) ?_ ?_ ?_ ?_
  · intro σ _
    have hxm : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
    have := σ.commutes (⟨x, hxm⟩ : Kx x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc] at this
    exact this
  · intro σ _ τ _ hst
    exact AlgHom.coe_ringHom_injective hst
  · intro φ' hφ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ'
    refine ⟨{ φ' with commutes' := fun r => ?_ }, Finset.mem_univ _, ?_⟩
    · exact eq_on_adjoin x φ' φ hφ' _ r.2
    · ext y; rfl
  · intro σ _
    rfl

private theorem conj_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.1 h
    have h2 : (r ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h

private theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) (a : E) :
    φ (conjE E a) = starRingEnd ℂ (φ a) := by
  have h : conjE E a = IsCMField.complexConj E a := rfl
  rw [h]
  exact (IsCMField.complexEmbedding_complexConj E φ a)

end UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings

open UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings in
theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normEmb :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmb := by
  classical
  intro E _ _ _ d x hd hx k
  have hsq : ∀ φ : E →+* ℂ, (φ x) ^ 2 = -(d : ℂ) := fun φ => by
    rw [← map_pow, hx]; simp
  have hne : ∀ φ : E →+* ℂ, φ x ≠ 0 := fun φ h0 => by
    have h1 := hsq φ
    rw [h0] at h1
    have h2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    apply h2
    simpa using h1.symm
  have hcj : ∀ φ : E →+* ℂ, φ (conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
      ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = -φ x), φ' k := by
    intro φ
    have h := norm_Kx x ((starRingEnd ℂ).comp φ) (k : E)
    simp only [RingHom.comp_apply, conj_of_sq hd (hsq φ)] at h
    rw [emb_conj, h]
  have hQ : ((Algebra.norm ℚ (k : E) : ℚ) : ℂ) = ∏ φ' : E →+* ℂ, φ' k := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ (k : E)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)
  let φ₀ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have hmul : φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E))) *
      φ₀ (conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
      ((Algebra.norm ℚ (k : E) : ℚ) : ℂ) := by
    rw [norm_Kx x φ₀ (k : E), hcj φ₀, hQ, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun φ' : E →+* ℂ => φ' x = φ₀ x)]
    congr 2
    ext φ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h2 : (φ' x) ^ 2 = (φ₀ x) ^ 2 := by rw [hsq, hsq]
    constructor
    · intro h h'
      rw [h] at h'
      have : (2 : ℂ) * φ₀ x = 0 := by linear_combination -h'
      exact hne φ₀ (by simpa using this)
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
      · exact absurd h3 h
      · exact h3
  refine ⟨hcj, hQ, ?_, ?_⟩
  · have ht : φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E))) ≠ 0 := by
      haveI : FiniteDimensional (Kx x) E := FiniteDimensional.right ℚ (Kx x) E
      rw [Ne, map_eq_zero, map_eq_zero, Algebra.norm_eq_zero_iff]
      exact k.ne_zero
    rw [emb_conj, Complex.mul_conj] at hmul
    have h1 : Complex.normSq (φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
        ((Algebra.norm ℚ (k : E) : ℚ) : ℝ) := by exact_mod_cast hmul
    have h2 := Complex.normSq_pos.2 ht
    rw [h1] at h2
    exact_mod_cast h2
  · apply φ₀.injective
    rw [map_mul, hmul]
    simp
