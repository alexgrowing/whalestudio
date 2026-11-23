import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.PowerSeriesExpansionImageDenseWithDenominator

noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))

theorem intVal_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.intValuation ϖ = exp (-1 : ℤ) := by
  have a1 : v.intValuation ϖ ≤ exp (-((1 : ℕ) : ℤ)) :=
    (intValuation_le_pow_iff_mem v ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ v.intValuation ϖ ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((intValuation_le_pow_iff_mem v ϖ 2).1 h)
  have h0 : v.intValuation ϖ ≠ 0 := by
    intro h; apply a2; rw [h]; simp
  rw [← exp_log h0] at a1 a2 ⊢
  rw [exp_le_exp] at a1 a2
  congr 1; push_cast at a1 a2; omega

theorem coe_j (r : 𝓞 E) :
    ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) r : v.adicCompletionIntegers E) :
      v.adicCompletion E) = algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E r) := rfl

theorem v_j (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) r : v.adicCompletionIntegers E) :
      v.adicCompletion E) = v.intValuation r := by
  rw [coe_j, adicCompl_val_algebraMap, valuation_of_algebraMap]

theorem detect_ideal {Q : Ideal (𝓞 E)} [Q.IsPrime] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q) (h2 : ϖ ∉ Q ^ 2)
    (x : 𝓞 E) (K : ℕ) (hx : x ∈ Q ^ K) : ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = ϖ ^ K * w := by
  obtain ⟨I, hI⟩ := Ideal.dvd_span_singleton.2 h1
  have hIQ : ¬ I ≤ Q := by
    intro h
    apply h2
    have : Ideal.span {ϖ} ≤ Q ^ 2 := by rw [hI, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self ϖ)
  have hIK : ¬ I ^ K ≤ Q := fun h => hIQ (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨s, hsI, hsQ⟩ := Set.not_subset.1 hIK
  have hm : s * x ∈ Ideal.span {ϖ ^ K} := by
    rw [← Ideal.span_singleton_pow, hI, mul_pow, mul_comm]
    exact Ideal.mul_mem_mul hsI hx
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨s, hsQ, w, by rw [← hw, mul_comm]⟩

section Sig

variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)

def sigR : v.adicCompletionIntegers E →+* v.adicCompletionIntegers E :=
  (sigK v hv).restrict (v.adicCompletionIntegers E) (v.adicCompletionIntegers E)
    (fun x hx => sigK_mem v hv x hx)

theorem sigR_coe (x : v.adicCompletionIntegers E) :
    ((sigR v hv x : v.adicCompletionIntegers E) : v.adicCompletion E) = sigK v hv x := rfl

theorem sigR_sigR (x : v.adicCompletionIntegers E) : sigR v hv (sigR v hv x) = x :=
  Subtype.ext (by rw [sigR_coe, sigR_coe, sigK_sigK])

def sigO : v.adicCompletionIntegers E ≃+* v.adicCompletionIntegers E :=
  RingEquiv.ofRingHom (sigR v hv) (sigR v hv)
    (RingHom.ext fun x => sigR_sigR v hv x) (RingHom.ext fun x => sigR_sigR v hv x)

theorem sigO_apply (x : v.adicCompletionIntegers E) : sigO v hv x = sigR v hv x := rfl

theorem sigO_sigO (x : v.adicCompletionIntegers E) : sigO v hv (sigO v hv x) = x := by
  rw [sigO_apply, sigO_apply]
  exact sigR_sigR v hv x

theorem j_cj (x : 𝓞 E) :
    algebraMap (𝓞 E) (v.adicCompletionIntegers E) (cj E x) =
      sigO v hv (algebraMap (𝓞 E) (v.adicCompletionIntegers E) x) :=
  Subtype.ext (by rw [sigO_apply, sigR_coe, coe_j, coe_j, sigK_int v hv])

end Sig

theorem modelEx_of (hF : FixedDVR) (hU : RealUnif) : ModelEx := by
  intro E _ _ _ hE Q hQ hcj
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
  let v : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hv : v.asIdeal.comap (cj E) = v.asIdeal := hcj
  obtain ⟨ϖ, hϖc, hϖQ, hϖ2⟩ := hU E hE Q hQ hcj
  have : v.asIdeal.IsMaximal := hQ
  have : Finite (ResidueField (v.adicCompletionIntegers E)) := adicInt_residue_finite (K := E) v
  have hval : Valued.v ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ :
      v.adicCompletionIntegers E) : v.adicCompletion E) = exp (-1 : ℤ) := by
    rw [v_j, intVal_unif v hϖQ hϖ2]
  have hirr : Irreducible (algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (adicInt_max_eq_span v _ hval)
  have hσϖ : sigO v hv (algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) =
      algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ := by
    rw [← j_cj v hv, hϖc]
  obtain ⟨hd, hh, hf, hirr0⟩ := hF _ (sigO v hv) (sigO_sigO v hv) _ hirr hσϖ
  have hmem : algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ ∈ fixSub (sigO v hv) := hσϖ
  obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 Q hQ
  have hθ : cj E θ = t := RingOfIntegers.ext (by rw [cj_coe]; exact ht.symm)
  exact ⟨{
    R := v.adicCompletionIntegers E
    σ := sigO v hv
    σσ := sigO_sigO v hv
    R₀ := fixSub (sigO v hv)
    mem₀ := mem_fixSub _
    dvr := hd
    hens := hh
    fin := hf
    unram := ⟨algebraMap (𝓞 E) (v.adicCompletionIntegers E) θ, by
      rw [← j_cj v hv, ← map_sub, hθ]
      exact adicInt_isUnit_of_not_mem v _ hθt⟩
    j := algebraMap (𝓞 E) (v.adicCompletionIntegers E)
    j_cj := j_cj v hv
    ϖ := ϖ
    ϖ_cj := hϖc
    ϖ_Q := hϖQ
    ϖ_mem := hmem
    ϖ_irr := hirr0 hmem
    unit_of := fun s hs => adicInt_isUnit_of_not_mem v s hs
    dense := by
      intro x K
      obtain ⟨y, hy⟩ := powerSeries_expansion_image_dense_with_denominator v x x.2 K
      have hle : Valued.v ((x - algebraMap (𝓞 E) (v.adicCompletionIntegers E) y :
          v.adicCompletionIntegers E) : v.adicCompletion E) ≤
          Valued.v (((algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) ^ K :
          v.adicCompletionIntegers E) : v.adicCompletion E) := by
        rw [SubmonoidClass.coe_pow, map_pow, hval, ← exp_nsmul, AddSubgroupClass.coe_sub, coe_j,
          Valuation.map_sub_swap]
        refine le_of_lt (lt_of_lt_of_eq hy ?_)
        congr 1; simp
      obtain ⟨z, hz⟩ := (adicInt_dvd_iff v _ _).2 hle
      exact ⟨y, z, hz⟩
    detect := by
      intro x K ⟨z, hz⟩
      have h1 : v.intValuation x ≤ exp (-(K : ℤ)) := by
        rw [← v_j, hz, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hval]
        calc exp (-1 : ℤ) ^ K * Valued.v (z : v.adicCompletion E)
            ≤ exp (-1 : ℤ) ^ K * 1 := by gcongr; exact z.2
          _ = exp (-(K : ℤ)) := by rw [mul_one, ← exp_nsmul]; congr 1; simp
      have : Q.IsPrime := hQ.isPrime
      exact detect_ideal hϖQ hϖ2 x K ((intValuation_le_pow_iff_mem v x K).1 h1) }⟩

end PI.SqPairLocal.Mdl

namespace PI.SqPairLocal

theorem modelEx_of (hF : FixedDVR) (hU : RealUnif) : ModelEx := Mdl.modelEx_of hF hU

end PI.SqPairLocal
