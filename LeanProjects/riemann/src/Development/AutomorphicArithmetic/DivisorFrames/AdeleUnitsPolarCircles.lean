import Mathlib
open NumberField IsDedekindDomain Filter Topology

private theorem polar_decomposition_circles {ι : Type} [Fintype ι] (K : ι → Type) [∀ w, Field (K w)]
    [∀ w, TopologicalSpace (K w)] (e : ∀ w, K w ≃+* ℂ) (he : ∀ w, Continuous (e w).symm)
    (B : Type) [CommMonoid B] [TopologicalSpace B] :
    ∃ c : ι → (Circle →* ((∀ w, K w) × B)ˣ), (∀ w, Continuous (c w)) ∧
      ∀ x : ((∀ w, K w) × B)ˣ, (x : (∀ w, K w) × B).2 = 1 →
        ∃ r : ((∀ w, K w) × B)ˣ, (r : (∀ w, K w) × B).2 = 1 ∧
          (∀ w, (e w ((r : (∀ w, K w) × B).1 w)).im = 0) ∧
          r⁻¹ * x ∈ ⨆ w, (c w).range := by
  classical
  let f : ι → (Circle →* ((∀ w, K w) × B)) := fun w =>
    (MonoidHom.inl _ _).comp ((MonoidHom.mulSingle K w).comp
      (((e w).symm : ℂ →+* K w).toMonoidHom.comp Circle.coeHom))
  have hf : ∀ w z, f w z = (Pi.mulSingle w ((e w).symm (z : ℂ)), 1) := fun w z => rfl
  have hfc : ∀ w, Continuous (f w) := fun w => by
    have : (f w : Circle → _) = fun z : Circle => (Pi.mulSingle w ((e w).symm (z : ℂ)), (1 : B)) :=
      funext (hf w)
    rw [this]
    exact ((continuous_mulSingle w).comp ((he w).comp continuous_subtype_val)).prodMk
      continuous_const
  refine ⟨fun w => (f w).toHomUnits, fun w => ?_, fun x hx => ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨hfc w, ?_⟩
    have : (fun z : Circle => (((f w).toHomUnits z)⁻¹ : ((∀ w, K w) × B)ˣ).val)
        = fun z => f w z⁻¹ := by
      funext z
      rw [← map_inv]; rfl
    exact this ▸ (hfc w).comp continuous_inv
  · have hz : ∀ w, e w ((x : (∀ w, K w) × B).1 w) ≠ 0 := fun w => by
      have h := congrArg (fun y : (∀ w, K w) × B => y.1 w) x.mul_inv
      simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] at h
      exact (map_ne_zero_iff _ (e w).injective).2 (left_ne_zero_of_mul_eq_one h)
    let t : ι → Circle := fun w => Circle.exp (Complex.arg (e w ((x : (∀ w, K w) × B).1 w)))
    let T : ((∀ w, K w) × B)ˣ := ∏ w, (f w).toHomUnits (t w)
    have hT : (T : (∀ w, K w) × B) = (fun w => (e w).symm (t w : ℂ), 1) := by
      simp only [T, Units.coe_prod, MonoidHom.coe_toHomUnits, hf]
      ext w
      · rw [Prod.fst_prod]
        exact congrFun (Finset.univ_prod_mulSingle (fun w => (e w).symm (t w : ℂ))) w
      · rw [Prod.snd_prod]; simp
    have hx' : ((x * T⁻¹ : ((∀ w, K w) × B)ˣ) : (∀ w, K w) × B) * T = x := by
      rw [← Units.val_mul]; simp
    refine ⟨x * T⁻¹, ?_, fun w => ?_, ?_⟩
    · have h := congrArg Prod.snd hx'
      rw [Prod.snd_mul, hT, hx] at h
      simpa using h
    · have h := congrArg (fun y : (∀ w, K w) × B => e w (y.1 w)) hx'
      simp only [Prod.fst_mul, Pi.mul_apply, hT, map_mul, RingEquiv.apply_symm_apply] at h
      have h2 := Complex.norm_mul_exp_arg_mul_I (e w ((x : (∀ w, K w) × B).1 w))
      have h3 : (t w : ℂ) = Complex.exp (Complex.arg (e w ((x : (∀ w, K w) × B).1 w)) * Complex.I) :=
        Circle.coe_exp _
      rw [← h3, ← h] at h2
      have h4 := mul_right_cancel₀ (t w).coe_ne_zero h2
      rw [← h4]
      exact Complex.ofReal_im _
    · have : (x * T⁻¹)⁻¹ * x = T := by
        rw [mul_inv, inv_inv, mul_right_comm, inv_mul_cancel, one_mul]
      rw [this]
      exact Subgroup.prod_mem _ fun w _ =>
        Subgroup.mem_iSup_of_mem w ⟨t w, rfl⟩

theorem UpperTheory.adele_units_polar_circles :
    ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
        ∃ c : InfinitePlace E → (Circle →* (AdeleRing (𝓞 E) E)ˣ), (∀ w, Continuous (c w)) ∧
          ∀ x : (AdeleRing (𝓞 E) E)ˣ, (x : AdeleRing (𝓞 E) E).2 = 1 →
            ∃ r : (AdeleRing (𝓞 E) E)ˣ, (r : AdeleRing (𝓞 E) E).2 = 1 ∧
              (∀ w : InfinitePlace E, (InfinitePlace.Completion.extensionEmbedding w ((r : AdeleRing (𝓞 E) E).1 w)).im = 0) ∧
              r⁻¹ * x ∈ ⨆ w, (c w).range := by
  intro E _ _ hE
  exact polar_decomposition_circles (fun w : InfinitePlace E => w.Completion)
    (fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (hE.isComplex w))
    (fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (hE.isComplex w)).symm.continuous)
    (FiniteAdeleRing (𝓞 E) E)
