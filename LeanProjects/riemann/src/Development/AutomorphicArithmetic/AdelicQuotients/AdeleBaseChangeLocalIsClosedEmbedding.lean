import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Topology Filter

private theorem ce_of_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) (h : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hf (Function.Injective.of_comp h.injective)
    (isProperMap_of_comp_of_t2 hf hg h.isProperMap).isClosedMap

private theorem ce_reindex {V : Type*} {A : V → Type*} [∀ v, TopologicalSpace (A v)] (φ : V → V) (h : ∀ v, φ v = v) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => x (φ v)) := by
  obtain rfl : φ = id := funext h
  exact (Homeomorph.refl _).isClosedEmbedding

private theorem ce_piMap {V : Type*} {A B : V → Type*} [∀ v, TopologicalSpace (A v)] [∀ v, TopologicalSpace (B v)]
    (ι : ∀ v, A v → B v) (h : ∀ v, IsClosedEmbedding (ι v)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => ι v (x v)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_pi fun v => (h v).continuous.comp (continuous_apply v))
    (fun _ _ e => funext fun v => (h v).injective (congrFun e v))
    (IsProperMap.pi_map fun v => (h v).isProperMap).isClosedMap

private theorem ce_pi {V W : Type*} (c : W → V) (hc : Function.Surjective c) {A : V → Type*} {B : W → Type*}
    [∀ v, TopologicalSpace (A v)] [∀ w, TopologicalSpace (B w)] [∀ w, T2Space (B w)]
    (ι : ∀ w, A (c w) → B w) (h : ∀ w, IsClosedEmbedding (ι w)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (w : W) => ι w (x (c w))) := by
  choose s hs using hc
  refine ce_of_comp (g := fun (y : ∀ w, B w) (v : V) => y (s v))
    (continuous_pi fun w => (h w).continuous.comp (continuous_apply _))
    (continuous_pi fun v => continuous_apply _) ?_
  exact (ce_piMap (fun v => ι (s v)) fun v => h (s v)).comp (ce_reindex (A := A) (fun v => c (s v)) hs)

private theorem ce_gl {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [T2Space R] [T2Space S] (n : ℕ) (f : R →+* S) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mapGL n f) := by
  have h1 : IsClosedEmbedding (fun (x : Fin n → R) (j : Fin n) => f (x j)) := ce_piMap (fun _ => f) fun _ => hf
  have hM : IsClosedEmbedding (f.mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) S) :=
    ce_piMap (fun _ => fun (x : Fin n → R) (j : Fin n) => f (x j)) fun _ => h1
  exact @IsClosedEmbedding.units_map (Matrix (Fin n) (Fin n) R) (Matrix (Fin n) (Fin n) S)
    _ _ _ _ _ _ f.mapMatrix.toMonoidHom hM

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_small (v : HeightOneSpectrum (𝓞 F)) (g : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ a : v.adicCompletion F, a ≠ 0 ∧ Valued.v a < (g : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hπ
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) π) < 1 := by
    rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h2 g
  refine ⟨algebraMap F (v.adicCompletion F) π ^ k, pow_ne_zero _ ?_, by rwa [map_pow]⟩
  intro h0
  rw [h0, map_zero] at h1
  exact (WithZero.exp_ne_zero) h1.symm

private theorem ce_compl (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    IsClosedEmbedding (completionMap v w) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 F)).ne'
  have hind : IsInducing (completionMap v w) := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    · have := (continuous_completionMap v w).tendsto 0
      rw [map_zero] at this
      exact this.le_comap
    · intro s hs
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
      obtain ⟨a, ha0, ha⟩ := exists_small v (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass (Valued.v : Valuation (v.adicCompletion F) _)))) γ)
      have hfa : completionMap v w a ≠ 0 := (map_ne_zero_iff _ (completionMap v w).injective).2 ha0
      have hopen := Valued.isOpen_ball (w.adicCompletion E) ((Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a))
      have hmem : (0 : w.adicCompletion E) ∈ {x | (Valued.v : Valuation (w.adicCompletion E) _).restrict x < (Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a)} := by
        simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Valuation.restrict_lt_iff, map_zero]
        exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hfa)
      refine Filter.mem_comap.2 ⟨_, hopen.mem_nhds hmem, fun x hx => hγ ?_⟩
      have h1 : Valued.v (completionMap v w x) < Valued.v (completionMap v w a) := by
        simpa [Valuation.restrict_lt_iff] using hx
      rw [valued_completionMap, valued_completionMap] at h1
      have h2 := lt_of_pow_lt_pow_left₀ _ zero_le' h1
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      exact h2.trans ha
  have hu : IsUniformInducing (completionMap v w) := AddMonoidHom.isUniformInducing_of_isInducing hind
  exact (IsUniformEmbedding.mk hu (completionMap v w).injective).isClosedEmbedding

private theorem ce_infComp (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] :
    IsClosedEmbedding (LiesOver.completionMap (v := v) (w := w)) := by
  have : Isometry (LiesOver.completionMap (v := v) (w := w)) := by
    refine AddMonoidHomClass.isometry_of_norm _ fun y => ?_
    refine InfinitePlace.Completion.induction_on v y
      (isClosed_eq LiesOver.continuous_completionMap.norm continuous_norm) fun a => ?_
    rw [LiesOver.completionMap_coe]
    have h := (InfinitePlace.LiesOver.isometry_algebraMap w v).norm_map_of_map_zero (map_zero _) a
    rw [InfinitePlace.Completion.norm_coe, InfinitePlace.Completion.norm_coe]
    exact h
  exact this.isClosedEmbedding

private theorem ce_incFin (v : HeightOneSpectrum (𝓞 F)) : IsClosedEmbedding (incFin E v) := by
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  let w : PlacesOver E v := (placesOverEquiv E v).symm P
  exact ce_of_comp (g := fun y : CompletionsOver E v => y w)
    (continuous_pi fun u => continuous_completionMap v u.1) (continuous_apply w) (ce_compl v w.1)

private theorem ce_infMap : IsClosedEmbedding (infMap F E) := by
  have hs : Function.Surjective (fun w : InfinitePlace E => w.comap (algebraMap F E)) := InfinitePlace.comap_surjective
  exact ce_pi (A := fun v : InfinitePlace F => v.Completion) (B := fun w : InfinitePlace E => w.Completion)
    (fun w : InfinitePlace E => w.comap (algebraMap F E)) hs
    (fun w => LiesOver.completionMap (v := w.comap (algebraMap F E)) (w := w)) fun w => ce_infComp _ w
end

theorem UpperTheory.adele_baseChange_local_isClosedEmbedding :
    LocEmb := by
  intro F E _ _ _ _ _ n
  exact ⟨ce_gl n _ ce_infMap, fun v => ce_gl n _ (ce_incFin v)⟩
