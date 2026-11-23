import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

noncomputable section

open MeasureTheory UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section Gen

variable {G : Type} [TopologicalSpace G]

private def WC {W : Type} [AddCommGroup W] [Module ℂ W] (f : G → W) : Prop :=
  ∀ φ : Module.Dual ℂ W, Continuous fun g => φ (f g)

private theorem wc_of_basis {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W) {f : G → W}
    (h : ∀ i, Continuous fun g => b.repr (f g) i) : WC f := by
  intro φ
  have e : (fun g => φ (f g)) = fun g => ∑ i, b.repr (f g) i * φ (b i) := by
    funext g
    conv_lhs => rw [← b.sum_repr (f g), map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finset_sum _ fun i _ => (h i).mul continuous_const

private theorem wc_hom {X Y : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] {f : G → (X →ₗ[ℂ] Y)} (h : ∀ x, WC fun g => f g x) : WC f := by
  classical
  refine wc_of_basis ((Module.finBasis ℂ X).linearMap (Module.finBasis ℂ Y)) fun i => ?_
  have := h (Module.finBasis ℂ X i.2) ((Module.finBasis ℂ Y).coord i.1)
  refine this.congr fun g => ?_
  simp [Module.Basis.linearMap, Matrix.stdBasis, Matrix.ofLinearEquiv, LinearMap.toMatrix_apply]

private theorem exists_wint [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {f : G → W} (hf : WC f) :
    ∃ q : W, ∀ φ : Module.Dual ℂ W, φ q = ∫ g, φ (f g) ∂ν := by
  let b := Module.finBasis ℂ W
  refine ⟨∑ i, (∫ g, b.coord i (f g) ∂ν) • b i, fun φ => ?_⟩
  have e : ∀ g, φ (f g) = ∑ i, b.coord i (f g) * φ (b i) := by
    intro g
    conv_lhs => rw [← b.sum_repr (f g), map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ =>
    ((hf (b.coord i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const _, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, map_smul, smul_eq_mul]

private theorem dual_ext {W : Type} [AddCommGroup W] [Module ℂ W] {x y : W}
    (h : ∀ φ : Module.Dual ℂ W, φ x = φ y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, h, sub_self]

private theorem tr_inv [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (τ : G → Module.End ℂ M) (hτ : ∀ g h, τ (g * h) = τ g * τ h) (hc : WC τ) (I : Submodule ℂ M)
    (hI : ∀ t, t ∈ I ↔ ∀ g, τ g t = t) (F : Module.End ℂ M) (hF : ∀ t ∈ I, F t ∈ I) :
    trOn I F = ∫ g, LinearMap.trace ℂ M (τ g * F) ∂ν := by
  obtain ⟨Q, hQ⟩ := exists_wint ν hc
  have h1 : ∀ g, τ g * Q = Q := fun g => dual_ext fun φ => by
    have := hQ (φ ∘ₗ LinearMap.mulLeft ℂ (τ g))
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← hτ] at this
    rw [this, hQ φ, integral_mul_left_eq_self (fun h => φ (τ h)) g]
  have h2 : ∀ t ∈ I, Q t = t := fun t ht => dual_ext fun φ => by
    have := hQ (φ ∘ₗ LinearMap.applyₗ t)
    simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, (hI t).1 ht] at this
    simpa using this
  have h3 : ∀ t, (Q * F) t ∈ I := fun t => (hI _).2 fun g => by
    have := LinearMap.congr_fun (h1 g) (F t)
    simpa using this
  have h4 := hQ (LinearMap.trace ℂ M ∘ₗ LinearMap.mulRight ℂ F)
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at h4
  rw [← h4, ← LinearMap.trace_restrict_eq_of_forall_mem I (Q * F) h3]
  unfold trOn
  rw [dif_pos hF]
  congr 1
  refine LinearMap.ext fun t => Subtype.ext ?_
  exact (h2 _ (hF t t.2)).symm

private theorem trOn_map' {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (j : M →ₗ[ℂ] N)
    (hj : Function.Injective j) (S : Submodule ℂ M) (f : Module.End ℂ M) (g : Module.End ℂ N) (hf : ∀ x ∈ S, f x ∈ S)
    (h : ∀ x, g (j x) = j (f x)) : trOn (S.map j) g = trOn S f := by
  have hg : ∀ y ∈ S.map j, g y ∈ S.map j := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, hf x hx, (h x).symm⟩
  unfold trOn
  rw [dif_pos hg, dif_pos hf, ← LinearMap.trace_conj' (f.restrict hf) (Submodule.equivMapOfInjective j hj S)]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (Submodule.equivMapOfInjective j hj S).surjective y
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact Subtype.ext (h x)

end Gen

section Fin

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem tr_dualT (E : KMod n) (T : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E T).toLinearMap = LinearMap.trace ℂ E.V (T : E.V →ₗ[ℂ] E.V) := by
  let e : (E.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  rw [← LinearMap.trace_transpose' (T : E.V →ₗ[ℂ] E.V), ← LinearMap.trace_conj' _ e]
  congr 1

private theorem tr_flipA [FiniteDimensional ℂ V] (E : KMod n) (A : Module.End ℂ V) (T : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ _ (flipA E A T) = LinearMap.trace ℂ E.V (T : E.V →ₗ[ℂ] E.V) * LinearMap.trace ℂ V A := by
  let e := dualTensorHomEquiv ℂ (E.V →L[ℂ] ℂ) V
  rw [← tr_dualT, ← LinearMap.trace_transpose' (dualT E T).toLinearMap, ← LinearMap.trace_tensorProduct',
    ← LinearMap.trace_conj' _ e]
  congr 1
  refine LinearMap.ext fun t => ?_
  obtain ⟨u, rfl⟩ := e.surjective t
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    refine LinearMap.ext fun ξ => ?_
    simp [e, flipA, Module.Dual.transpose_apply]

private theorem mem_invA (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) (t : (E.V →L[ℂ] ℂ) →ₗ[ℂ] V) :
    t ∈ invA σ E ↔ ∀ g, flipA E (σ g) (E.ρ g) t = t := by
  have e : ∀ (g : Un n) (ξ : E.V →L[ℂ] ℂ), (ξ ∘L E.ρ g) ∘L E.ρ g⁻¹ = ξ := fun g ξ => by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
    rfl
  constructor
  · intro ht g
    refine LinearMap.ext fun ξ => ?_
    show σ g (t (ξ ∘L E.ρ g)) = t ξ
    rw [← ht g, e]
  · intro ht g ξ
    have h : σ g (t ((ξ ∘L E.ρ g⁻¹) ∘L E.ρ g)) = t (ξ ∘L E.ρ g⁻¹) := LinearMap.congr_fun (ht g) _
    have e' := e g⁻¹ ξ
    rw [inv_inv] at e'
    rw [← h, e']

private theorem flipA_mul (E : KMod n) (A B : Module.End ℂ V) (T U : E.V →L[ℂ] E.V) :
    flipA E A T * flipA E B U = flipA E (A * B) (T * U) := rfl

private theorem flip_mem (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) {T : E.V →L[ℂ] E.V} {A : Module.End ℂ V}
    (hT : ∀ k, T * E.ρ k = E.ρ k * T) (hA : ∀ k, A * σ k = σ k * A) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht
  rw [mem_invA] at ht ⊢
  intro g
  rw [← Module.End.mul_apply, flipA_mul, ← hT, ← hA, ← flipA_mul, Module.End.mul_apply, ht g]

private theorem wc_flip [FiniteDimensional ℂ V] (σ : Un n →* (V →ₗ[ℂ] V))
    (hσ : ∀ v w : V, Continuous fun k => ⟪w, σ k v⟫_ℂ) (E : KMod n) : WC fun g => flipA E (σ g) (E.ρ g) := by
  let b := stdOrthonormalBasis ℂ V
  refine wc_hom fun t => wc_hom fun ξ => wc_of_basis b.toBasis fun i => ?_
  have hv : Continuous fun g : Un n => t (ξ ∘L E.ρ g) :=
    t.continuous_of_finiteDimensional.comp (continuous_const.clm_comp E.cont)
  have e : ∀ g : Un n, b.toBasis.repr (flipA E (σ g) (E.ρ g) t ξ) i =
      ∑ j, ⟪b j, t (ξ ∘L E.ρ g)⟫_ℂ * ⟪b i, σ g (b j)⟫_ℂ := by
    intro g
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    show ⟪b i, σ g (t (ξ ∘L E.ρ g))⟫_ℂ = _
    conv_lhs => rw [← b.sum_repr' (t (ξ ∘L E.ρ g))]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  simp_rw [e]
  exact continuous_finset_sum _ fun j _ => (continuous_const.inner hv).mul (hσ _ _)

private theorem fin_case [FiniteDimensional ℂ V] [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (σ : Un n →* (V →ₗ[ℂ] V))
    (hσ : ∀ v w : V, Continuous fun k => ⟪w, σ k v⟫_ℂ) (E : KMod n) (T : E.V →L[ℂ] E.V) (P A : Module.End ℂ V)
    (hT : ∀ k, T * E.ρ k = E.ρ k * T) (hP : IsAvg ν σ E T P) (hA : ∀ k, A * σ k = σ k * A) :
    LinearMap.trace ℂ V (P * A) = trOn (invA σ E) (flipA E A T) := by
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  rw [tr_inv ν (fun g => flipA E (σ g) (E.ρ g)) (fun g h => by simp only [flipA_mul, map_mul]) (wc_flip σ hσ E)
    (invA σ E) (mem_invA σ E) _ (flip_mem σ E hT hA)]
  simp only [flipA_mul, tr_flipA]
  let b := stdOrthonormalBasis ℂ V
  have hc : Continuous fun κ : Un n => LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    ((LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)).continuous_of_finiteDimensional.comp
      (E.cont.mul continuous_const)
  simp_rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum, Module.End.mul_apply, hP _ _]
  exact (integral_finset_sum _ fun i _ =>
    (hc.mul (hσ _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).symm

private theorem iso_stable (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) {A : Module.End ℂ V}
    (hA : ∀ t ∈ invA σ E, ∀ ξ, ∃ t' ∈ invA σ E, ∃ ξ', A (t ξ) = t' ξ') : ∀ x ∈ isoSp σ E, A x ∈ isoSp σ E := by
  intro x hx
  have : isoSp σ E ≤ (isoSp σ E).comap A := by
    refine iSup_le ?_
    rintro t _ ⟨ξ, rfl⟩
    obtain ⟨t', ht', ξ', h⟩ := hA t.1 t.2 ξ
    exact (le_iSup (fun s : invA σ E => LinearMap.range s.1) ⟨t', ht'⟩) ⟨ξ', h.symm⟩
  exact this hx

end Fin

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.avgTr :
    AvgFacts → AvgTr := by
  intro hF n _ _ ν _ hν V _ _ σ hσ E T P A hT hP hA hfd
  haveI : IsProbabilityMeasure ν := ⟨hν⟩
  set S := isoSp σ E with hS
  have hPS : ∀ x, P x ∈ S := (hF n ν V σ hσ E T P hT hP).1
  have hσS : ∀ k, ∀ x ∈ S, σ k x ∈ S := fun k =>
    iso_stable σ E fun t ht ξ => ⟨t, ht, _, (ht k ξ).symm⟩
  have hAS : ∀ x ∈ S, A x ∈ S :=
    iso_stable σ E fun t ht ξ => ⟨_, flip_mem σ E (T := 1) (fun k => by simp) hA t ht, ξ, rfl⟩
  let σ' : Un n →* (S →ₗ[ℂ] S) :=
    { toFun := fun k => (σ k).restrict (hσS k)
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by simp) }
  let j : ((E.V →L[ℂ] ℂ) →ₗ[ℂ] S) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V) := LinearMap.llcomp ℂ _ S V S.subtype
  have hj : Function.Injective j := fun a b h =>
    LinearMap.ext fun ξ => Subtype.ext (LinearMap.congr_fun h ξ)
  have hmap : invA σ E = (invA σ' E).map j := by
    refine le_antisymm (fun t ht => ?_) ?_
    · have hm : ∀ ξ, t ξ ∈ S := fun ξ =>
        (le_iSup (fun s : invA σ E => LinearMap.range s.1) ⟨t, ht⟩) ⟨ξ, rfl⟩
      exact ⟨t.codRestrict S hm, fun k ξ => Subtype.ext (ht k ξ), rfl⟩
    · rintro _ ⟨t, ht, rfl⟩ k ξ
      exact congrArg Subtype.val (ht k ξ)
  have hA' : ∀ k, A.restrict hAS * σ' k = σ' k * A.restrict hAS := fun k =>
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (hA k) x.1)
  refine ⟨?_, fun hne hb => hne ?_, ?_⟩
  · rw [hmap]
    infer_instance
  · refine iSup_eq_bot.2 fun t => ?_
    have ht : t.1 ∈ (⊥ : Submodule ℂ ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V)) := hb ▸ t.2
    rw [(Submodule.mem_bot ℂ).1 ht, LinearMap.range_zero]
  · have hPA : ∀ x ∈ S, (P * A) x ∈ S := fun x _ => hPS _
    rw [hmap, trOn_map' j hj _ (flipA E (A.restrict hAS) T) _ (flip_mem σ' E hT hA') (fun _ => rfl),
      ← fin_case ν σ' (fun v w => hσ.cont v.1 w.1) E T (P.restrict fun x _ => hPS x) (A.restrict hAS) hT
        (fun v w => hP v.1 w.1) hA']
    unfold trOn
    rw [dif_pos hPA]
    rfl
