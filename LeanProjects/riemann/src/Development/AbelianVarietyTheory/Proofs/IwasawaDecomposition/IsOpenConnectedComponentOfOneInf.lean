import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem exists_units_hom {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field K] [TopologicalSpace K]
    (F : Γ →* K) (hF : Continuous F) : ∃ f : Γ →* Kˣ, Continuous f ∧ ∀ x, ((f x : Kˣ) : K) = F x :=
  ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩

theorem exists_infPow_hom : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* ℂˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : ℂˣ) : ℂ) = infPow n x := by
  intro E _ _ n
  have h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w =>
    @Fintype.ofFinite _ (finite_contEmbInf w)
  have e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i},
      i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion)) := fun x =>
    Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
  let F : Ideles E →* ℂ :=
    { toFun := infPow n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (infPow n)
  rw [funext e]
  refine continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

theorem exists_lPow_hom : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* (Qbar l)ˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : (Qbar l)ˣ) : Qbar l) = lPow ι n x := by
  intro E _ _ l _ ι n
  have hl : l.Prime := Fact.out
  have h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v =>
    @Fintype.ofFinite _ (finite_contEmb v)
  have hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset,
      ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^
        n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) := fun x => by
    unfold lPow
    rw [finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]
    · exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
    · intro v hv
      by_contra h
      refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
      exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))
  let F : Ideles E →* Qbar l :=
    { toFun := lPow ι n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (lPow ι n)
  rw [funext e]
  refine continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))

theorem infPow_diagUnits : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ), infPow n (diagUnits E k) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ := by
  intro E _ _ n k
  classical
  let J : InfinitePlace E → Type := fun w => {i : w.Completion →+* ℂ // Continuous i}
  let res : (Σ w, J w) → (E →+* ℂ) := fun p => p.2.1.comp (algebraMap E p.1.Completion)
  have hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion) := fun w => by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  have hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1 := by
    rintro ⟨w, i⟩
    have hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖ := fun y => by
      rcases w.isReal_or_isComplex with hw | hw
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry
        have h1 := Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom)
          (i.2.comp he.continuous) with h1 | h1
        · exact congrArg norm (DFunLike.congr_fun h1 z)
        · exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)
    refine InfinitePlace.ext _ _ fun a => ?_
    rw [InfinitePlace.apply]
    exact (hn _).trans (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    obtain rfl : v = v' := (hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (hd v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨j, hj, e⟩ := GlobalTheory.InfTypeLocal.exists_ext φ
    exact ⟨⟨_, j, hj⟩, RingHom.ext e⟩
  haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)
  rw [← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl,
    Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _

theorem isOpenEmbedding_val_inf (E : Type) [Field E] [NumberField E] :
    Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
  Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)

theorem isOpen_connectedComponentOfOne_inf : ∀ (E : Type) [Field E] [NumberField E], IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) : Set (InfiniteAdeleRing E)ˣ) := by
  intro E _ _
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace
  exact isOpen_connectedComponent

theorem denseRange_units_inf : ∀ (E : Type) [Field E] [NumberField E], DenseRange (fun k : Eˣ => (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ)) := by
  intro E _ _
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open
    ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [map_zero] at hk
    have h1 := congrFun v.mul_inv w
    rw [hk, zero_mul] at h1
    exact zero_ne_one (α := w.Completion) h1
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem pos_of_mem_connectedComponentOfOne : ∀ (E : Type) [Field E] [NumberField E] (k : Eˣ), (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ → ∀ φ : E →+* ℝ, 0 < φ (k : E) := by
  intro E _ _ k hk φ
  obtain ⟨e, he, hek⟩ := GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)
  let w := InfinitePlace.mk (Complex.ofRealHom.comp φ)
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  have him : ∀ y : w.Completion, (e y).im = 0 := fun y =>
    congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he)
      continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => (e ((u : InfiniteAdeleRing E) w)).re
  have hg : Continuous g :=
    Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : e ((u : InfiniteAdeleRing E) w) = 0 := Complex.ext h (him _)
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)
  have hg1 : g 1 = 1 := by
    show (e 1).re = 1
    simp
  have hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k := by
    show (e (algebraMap E _ (k : E))).re = _
    rw [hek]
    simp
  by_contra hneg
  have := isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  obtain ⟨u, -, hu⟩ := this
  exact hg0 u hu

end GlobalTheory.HeckeGal

end
