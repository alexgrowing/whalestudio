import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SigmaFiniteOfMp

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac.HS

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH hermMap)
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hermVec_hermV (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (y : HermR (Af F) σ n) (i : Idx n d) :
    hermVec (Fv F v) σ b n (hermV σ v y) i = evalV F v (hermVec (Af F) σ b n y i) :=
  hermVec_map (evalV F v) σ b n y i

omit [NumberField E] in

theorem mem_latH_iff_vec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (S : HermR (Fv F v) σ n) :
    S ∈ latH σ b v n ↔ ∀ i, hermVec (Fv F v) σ b n S i ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩ i
    cases i with
    | inl i => exact h1 i
    | inr q => exact h2 q.1.1.1 q.1.1.2 q.1.2 q.2
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i j hij k => h (Sum.inr (⟨(i, j), hij⟩, k))⟩

theorem continuous_hermV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (hermV σ v : HermR (Af F) σ n → HermR (Fv F v) σ n) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  letI : MeasurableSpace (Af F) := borel _
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨d, b⟩ : ∃ d, Nonempty (Module.Basis (Fin d) F E) := by
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
    exact ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨b⟩ := b
  let ef := (hermVec_isHomeomorph hCM (Af F) b n).homeomorph _
  let ev := (hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _
  have h : (hermV σ v : HermR (Af F) σ n → HermR (Fv F v) σ n) =
      ev.symm ∘ (fun x i => evalV F v (x i)) ∘ ef := by
    funext y
    apply ev.injective
    rw [show (ev.symm ∘ (fun x i => evalV F v (x i)) ∘ ef) y = ev.symm (fun i => evalV F v (ef y i)) from rfl,
      ev.apply_symm_apply]
    funext i
    exact hermVec_hermV σ b n v y i
  rw [h]
  refine ev.symm.continuous.comp (Continuous.comp ?_ ef.continuous)
  exact continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem coordHerm_box (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (hA : ∀ v, MeasurableSet (A v)) :
    coordHerm (Af F) σ b lf n {y | (∀ v ∈ S, hermV σ v y ∈ A v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} =
      ∏ v ∈ S, coordHerm (Fv F v) σ b (lam v) n (A v) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  let ef := ((hermVec_isHomeomorph hCM (Af F) b n).homeomorph _).toMeasurableEquiv
  let ev := fun v => ((hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _).toMeasurableEquiv
  have hef : ∀ y, ef y = hermVec (Af F) σ b n y := fun _ => rfl
  have hev : ∀ v y, ev v y = hermVec (Fv F v) σ b n y := fun _ _ => rfl
  have hF : MeasurePreserving ef (coordHerm (Af F) σ b lf n) (Measure.pi fun _ : Idx n d => lf) :=
    mp_hermVec hCM (Af F) b n lf
  have hV : ∀ v, MeasurePreserving (ev v) (coordHerm (Fv F v) σ b (lam v) n) (Measure.pi fun _ : Idx n d => lam v) :=
    fun v => mp_hermVec hCM (Fv F v) b n (lam v)
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Idx n d → Fv F v) := fun v => (ev v).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (ev v).symm.measurable (hA v)
  have hset : ({y | (∀ v ∈ S, hermV σ v y ∈ A v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} :
        Set (HermR (Af F) σ n)) = ef ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext y
    have hc : ∀ v, (fun i => evalV F v (ef y i)) = ev v (hermV σ v y) := fun v => by
      funext i
      exact (hermVec_hermV σ b n v y i).symm
    have hsy : ∀ v, (ev v).symm (fun i => evalV F v (ef y i)) = hermV σ v y := fun v =>
      (congrArg (ev v).symm (hc v)).trans ((ev v).symm_apply_apply _)
    have hl : ∀ v, (hermV σ v y ∈ latH σ b v n ↔ ∀ i, evalV F v (ef y i) ∈ v.adicCompletionIntegers F) := fun v =>
      (mem_latH_iff_vec σ b n v (hermV σ v y)).trans (forall_congr' fun i => Iff.of_eq
        (congrArg (fun t => t ∈ v.adicCompletionIntegers F) (hermVec_hermV σ b n v y i)))
    simp only [Set.mem_setOf_eq, Set.mem_preimage, A', hsy]
    exact and_congr Iff.rfl (forall_congr' fun v => imp_congr_right fun _ => hl v)
  rw [hset, hF.measure_preimage_equiv, GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Idx n d) S A' hA']
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← (hV v).measure_preimage_equiv]
  congr 1
  ext x
  simp [A']

def hV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermV σ v y

def intHR (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))}

theorem map_restrict_intH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ((coordHerm (Af F) σ b lf n).restrict (intHR σ b n S)).map (fun y (v : S) => hV σ v.1 y) =
      Measure.pi fun v : S => coordHerm (Fv F v.1) σ b (lam v.1) n := by
  classical
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  have hSF : ∀ v, SigmaFinite (coordHerm (Fv F v) σ b (lam v) n) := fun v =>
    haveI : SigmaFinite (lam v) := Measure.IsAddHaarMeasure.sigmaFinite (lam v)
    sigmaFinite_of_mp ((hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _).toMeasurableEquiv
      (mp_hermVec hCM (Fv F v) b n (lam v))
  haveI : ∀ v : S, SigmaFinite (coordHerm (Fv F v.1) σ b (lam v.1) n) := fun v => hSF v.1
  have hρ : Measurable (fun y (v : S) => hV σ v.1 y) :=
    measurable_pi_lambda _ fun v => (continuous_hermV σ hCM n v.1).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n) :=
    fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
    by_cases h : v ∈ S
    · simp only [A', dif_pos h]; exact hs _
    · simp only [A', dif_neg h]; exact MeasurableSet.univ
  have key := coordHerm_box σ hCM b lam hlam lf hlf h1 n S A' hA'
  have hset : (fun y (v : S) => hV σ v.1 y) ⁻¹' Set.univ.pi s ∩ intHR σ b n S =
      ({y | (∀ v ∈ S, hermV σ v y ∈ A' v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} : Set (HermR (Af F) σ n)) := by
    ext y
    change (∀ v : S, v ∈ Set.univ → hV σ v.1 y ∈ s v) ∧ (∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))) ↔
      (∀ v ∈ S, hV σ v y ∈ A' v) ∧ ∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))
    refine and_congr ⟨fun h v hv => ?_, fun h v _ => ?_⟩ Iff.rfl
    · simpa only [A', dif_pos hv] using h ⟨v, hv⟩ (Set.mem_univ _)
    · have := h v.1 v.2
      simpa only [A', dif_pos v.2] using this
  rw [hset, key, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', dif_pos v.2]

end PositivityTheory.SiegelWeilFormula.GFac.HS

end
