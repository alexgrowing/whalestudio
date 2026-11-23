import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompositumCompletion

theorem exists_completion_map {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L']
    (jL : L →+* L') (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L'))
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) :
    ∃ μ : v.adicCompletion L →+* v'.adicCompletion L', Continuous μ ∧
      ∀ x, μ (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  letI : Algebra L L' := jL.toAlgebra
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨by ext x; exact (h x).symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver L L' v v').continuous
  let φ : v.adicCompletion L →+* v'.adicCompletion L' :=
    ((HeightOneSpectrum.adicCompletion.equiv L' v').symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L'))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv L v).toRingHom
  refine ⟨φ, ?_, fun x => ?_⟩
  · exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' v').comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation L)) (WithVal (v'.valuation L')))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v))
  · apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)

theorem exists_ringEquiv_completion : ∀ (E L E' L' : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [Field E'] [NumberField E'] [Field L'] [NumberField L'] [Algebra E' L'] (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 E')) (v' : HeightOneSpectrum (𝓞 L')) (j : E →+* E') (jL : L →+* L') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal ↔ x ∈ w.asIdeal) → (∀ x : 𝓞 E', algebraMap (𝓞 E') (𝓞 L') x ∈ v'.asIdeal ↔ x ∈ w'.asIdeal) → (∀ x : 𝓞 L, RingOfIntegers.mapRingHom jL x ∈ v'.asIdeal ↔ x ∈ v.asIdeal) → (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∃ iL : v.adicCompletion L ≃+* v'.adicCompletion L', Continuous iL ∧ ∀ x, iL (algebraMap L _ x) = algebraMap L' _ (jL x) := by
  intro E L E' L' _ _ _ _ _ _ _ _ _ _ w v w' v' j jL i hv hv' hjv hjL hadj hic hij
  obtain ⟨κ, hκc, hκ⟩ := exists_completion_map (algebraMap E L) w v (fun x => hv x)
  obtain ⟨κ', hκ'c, hκ'⟩ := exists_completion_map (algebraMap E' L') w' v' (fun x => hv' x)
  obtain ⟨μ, hμc, hμ⟩ := exists_completion_map jL v v' hjv
  have hcomm : ∀ a, μ (κ a) = κ' (i a) := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer (hμc.comp hκc) (hκ'c.comp hic)
      (funext fun x => by simp only [Function.comp_apply, hκ, hμ, hjL, hij, hκ'])) a
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := E) (M := L)
  have hrange : Set.range jL ⊆ Submodule.span E' (jL '' (s : Set L)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span E (s : Set L) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul, hjL, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha
  have htop : Submodule.span E' (Set.range jL) = ⊤ := by
    have h1 := Algebra.adjoin_eq_span E' (Set.range jL)
    rw [hadj, Algebra.top_toSubmodule] at h1
    have hcl : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL :=
      congrArg SetLike.coe (Submonoid.closure_eq (MonoidHom.mrange jL))
    rw [h1, hcl]
  have hspan : ∀ y : L', y ∈ Submodule.span E' (jL '' (s : Set L)) := fun y => by
    have hy : y ∈ Submodule.span E' (Set.range jL) := htop ▸ Submodule.mem_top
    exact (Submodule.span_le.2 hrange) hy
  letI : Algebra (w'.adicCompletion E') (v'.adicCompletion L') := κ'.toAlgebra
  haveI : ContinuousSMul (w'.adicCompletion E') (v'.adicCompletion L') :=
    continuousSMul_of_algebraMap _ _ hκ'c
  letI : NontriviallyNormedField (w'.adicCompletion E') := Valued.toNontriviallyNormedField _ _
  let M : Submodule (w'.adicCompletion E') (v'.adicCompletion L') :=
    Submodule.span _ ((fun y => algebraMap L' (v'.adicCompletion L') (jL y)) '' (s : Set L))
  haveI : FiniteDimensional (w'.adicCompletion E') M :=
    FiniteDimensional.span_of_finite _ (s.finite_toSet.image _)
  have hcl : IsClosed (M : Set (v'.adicCompletion L')) := Submodule.closed_of_finiteDimensional _
  have hM : ∀ y : L', algebraMap L' (v'.adicCompletion L') y ∈ M := fun y => by
    induction hspan y using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : algebraMap L' (v'.adicCompletion L') (c • a) =
          (algebraMap E' (w'.adicCompletion E') c) • algebraMap L' (v'.adicCompletion L') a := by
        rw [Algebra.smul_def c a, map_mul, ← hκ']; rfl
      rw [e]; exact Submodule.smul_mem _ _ ha
  have hMμ : ∀ z ∈ M, z ∈ Set.range μ := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, _, rfl⟩ := hz
      exact ⟨algebraMap L _ x, hμ x⟩
    | zero => exact ⟨0, map_zero μ⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' + b', map_add μ a' b'⟩
    | smul c a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨κ (i.symm c) * a', by rw [map_mul, hcomm, i.apply_symm_apply]; rfl⟩
  have hsurj : Function.Surjective μ := fun y => by
    have hy : y ∈ (M : Set (v'.adicCompletion L')) :=
      (HeightOneSpectrum.denseRange_algebraMap L' v').induction_on
        (p := fun y => y ∈ (M : Set (v'.adicCompletion L'))) y hcl hM
    exact hMμ y hy
  exact ⟨RingEquiv.ofBijective μ ⟨μ.injective, hsurj⟩, hμc, fun x => hμ x⟩

end GlobalTheory.CompositumCompletion
