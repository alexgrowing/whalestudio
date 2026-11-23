import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlaces
import GroundTheory.GlobalFields.LocalAtPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

private theorem dense_of_approx {F K : Type} [Field F] [Field K] [NumberField K] (f : F →+* K)
    (w : HeightOneSpectrum (𝓞 K))
    (H : ∀ k a : K, a ≠ 0 → ∃ x : F, w.valuation K ((f x - k) / a) ≤ 1) :
    DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap K w
  refine Dense.of_closure (hd.mono ?_)
  rintro _ ⟨k, rfl⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [c]
  obtain ⟨a, ha⟩ := w.valuation_surjective K (c * WithZero.exp (-1 : ℤ))
  have ha1 : w.valuation K a ≠ 0 := by rw [ha]; exact mul_ne_zero hc0 WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha1
  obtain ⟨x, hx⟩ := H k a ha0
  refine ⟨_, hγ ?_, x, rfl⟩
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ha1), ha] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc, ← map_sub]
  have h1 : (Valued.v (algebraMap K (w.adicCompletion K) (f x - k)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x - k) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  rw [h1]
  refine hx.trans_lt ?_
  refine mul_lt_of_lt_one_right (zero_lt_iff.2 hc0) ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

private theorem surj_of_dense {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] (f : F →+* K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : F, w.valuation K (f x) ≤ 1 → v.valuation F x ≤ 1)
    (hd : DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x))
    (κ : v.adicCompletion F →+* w.adicCompletion K) (hc : Continuous κ)
    (hκ : ∀ x, κ (algebraMap F _ x) = algebraMap K _ (f x)) : Function.Surjective κ := by
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hcl := (hcomp.image hc).isClosed
  have ho : IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := Valued.isOpen_valuationSubring _
  have key : (w.adicCompletionIntegers K : Set (w.adicCompletion K)) ⊆ κ '' (v.adicCompletionIntegers F) := by
    refine (Dense.open_subset_closure_inter hd ho).trans (closure_minimal ?_ hcl)
    rintro _ ⟨h1, x, rfl⟩
    refine ⟨algebraMap F _ x, ?_, hκ x⟩
    have h2 : (Valued.v (algebraMap K (w.adicCompletion K) (f x)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : (Valued.v (algebraMap F (v.adicCompletion F) x) : WithZero (Multiplicative ℤ)) =
      v.valuation F x := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [h3]
    exact hv x (h2 ▸ h1)
  intro y
  rcases (w.adicCompletionIntegers K).mem_or_inv_mem y with h | h
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x, hx⟩
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩

theorem UpperTheory.V.Af.Cq.exPlaceIso :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O),
        Induces Bw → (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w)
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A v h O _ _ _ Bw hj hK
  obtain ⟨w, hw⟩ := place_between (L := K) h
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (algebraMap F K) v w (fun x => by
    rw [← hw, ← h x]
    show A.valuation (algebraMap K Ω (algebraMap F K x)) < 1 ↔ _
    rw [← IsScalarTower.algebraMap_apply])
  have hd := dense_of_approx (algebraMap F K) w (fun k a ha => by
    have hpos : 0 < ‖Bw.j (algebraMap K Ω a)‖ := by simpa using ha
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (hK k)) _ hpos
    refine ⟨x, ?_⟩
    rw [← TraceCompl.algebraMap_mem_iff hw, hj, map_div₀, map_div₀, norm_div, div_le_one hpos, map_sub, map_sub,
      ← IsScalarTower.algebraMap_apply, ← dist_eq_norm, dist_comm]
    exact hx.le)
  have hs := surj_of_dense (algebraMap F K) v w (fun x hx => by
    rw [← TraceCompl.algebraMap_mem_iff hw, ← IsScalarTower.algebraMap_apply,
      TraceCompl.algebraMap_mem_iff h] at hx
    exact hx) hd κ hκc hκ
  exact ⟨w, hw, RingEquiv.ofBijective κ ⟨κ.injective, hs⟩, fun _ => Iff.rfl,
    fun x => IsScalarTower.algebraMap_apply F K Ω x, hκc, hκ⟩
