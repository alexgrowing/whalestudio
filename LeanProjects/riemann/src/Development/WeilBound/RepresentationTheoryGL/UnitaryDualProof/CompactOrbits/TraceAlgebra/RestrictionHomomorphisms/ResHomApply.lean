import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace

noncomputable section

open Module

namespace PositivityTheory.RgUd.T.Alg.Iso2

variable {k : Type} [Field k] [CharZero k]

theorem iso_of_field {K W W' : Type} [Field K] [Algebra k K] [FiniteDimensional k K]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (σ : K →ₐ[k] Module.End k W) (σ' : K →ₐ[k] Module.End k W') (h : finrank k W = finrank k W') :
    ∃ φ : W ≃ₗ[k] W', ∀ c w, φ (σ c w) = σ' c (φ w) := by
  classical
  letI : Module K W := Module.compHom W σ.toRingHom
  letI : Module K W' := Module.compHom W' σ'.toRingHom
  haveI : IsScalarTower k K W := ⟨fun a c w => by
    show σ (a • c) w = a • σ c w
    rw [map_smul]
    rfl⟩
  haveI : IsScalarTower k K W' := ⟨fun a c w => by
    show σ' (a • c) w = a • σ' c w
    rw [map_smul]
    rfl⟩
  haveI : FiniteDimensional K W := Module.Finite.of_restrictScalars_finite k K W
  haveI : FiniteDimensional K W' := Module.Finite.of_restrictScalars_finite k K W'
  have hK : 0 < finrank k K := Module.finrank_pos
  have h2 : finrank K W = finrank K W' := by
    apply Nat.eq_of_mul_eq_mul_left hK
    rw [Module.finrank_mul_finrank, Module.finrank_mul_finrank, h]
  let ψ : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq W W' h2
  refine ⟨ψ.restrictScalars k, fun c w => ?_⟩
  exact ψ.map_smul c w

variable {n : ℕ} {R : Type} [CommRing R] [Algebra k R]

def resHom (ρ : R →ₐ[k] Module.End k (Fin n → k)) (e : R) :
    R →ₐ[k] Module.End k (LinearMap.range (ρ e)) where
  toFun r := (ρ r).restrict (p := LinearMap.range (ρ e)) (q := LinearMap.range (ρ e)) (fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨ρ r y, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm])
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]

theorem resHom_apply (ρ : R →ₐ[k] Module.End k (Fin n → k)) (e r : R) (x : LinearMap.range (ρ e)) :
    ((resHom ρ e r x : LinearMap.range (ρ e)) : Fin n → k) = ρ r x := rfl

end PositivityTheory.RgUd.T.Alg.Iso2

namespace PositivityTheory.RgUd.T.Alg.Iso2

open Module

variable {k : Type} [Field k] [CharZero k]

theorem proj_of_mem {n : ℕ} {R : Type} [CommRing R] [Algebra k R] (ρ : R →ₐ[k] Module.End k (Fin n → k))
    {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ I J, e I * e J = if I = J then e I else 0) (I J : ι)
    (x : Fin n → k) (hx : x ∈ LinearMap.range (ρ (e I))) : ρ (e J) x = if I = J then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, ← map_mul, he J I]
  by_cases h : I = J
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem comp_lemma {n : ℕ} {R : Type} [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)) (e : R) (he : e * e = e)
    (m : Ideal R) [m.IsMaximal] (hm : ∀ a ∈ m, a * e = 0)
    (htr : LinearMap.trace k (Fin n → k) (ρ e) = LinearMap.trace k (Fin n → k) (ρ' e)) :
    ∃ φ : LinearMap.range (ρ e) ≃ₗ[k] LinearMap.range (ρ' e),
      ∀ r x, φ (resHom ρ e r x) = resHom ρ' e r (φ x) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional k (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
  have h0 : ∀ (σ : R →ₐ[k] Module.End k (Fin n → k)), ∀ a ∈ m, resHom σ e a = 0 := by
    intro σ a ha
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    rw [resHom_apply, ← hy, ← Module.End.mul_apply, ← map_mul, hm a ha]
    simp
  have hI : ∀ σ : R →ₐ[k] Module.End k (Fin n → k), IsIdempotentElem (σ e) := fun σ => by
    show σ e * σ e = σ e
    rw [← map_mul, he]
  have hdim : finrank k (LinearMap.range (ρ e)) = finrank k (LinearMap.range (ρ' e)) := by
    have h1 := htr
    rw [(LinearMap.IsIdempotentElem.isProj_range _ (hI ρ)).trace,
      (LinearMap.IsIdempotentElem.isProj_range _ (hI ρ')).trace] at h1
    exact_mod_cast h1
  obtain ⟨φ, hφ⟩ := iso_of_field (Ideal.Quotient.liftₐ m (resHom ρ e) (h0 ρ))
    (Ideal.Quotient.liftₐ m (resHom ρ' e) (h0 ρ')) hdim
  refine ⟨φ, fun r x => ?_⟩
  exact hφ (Ideal.Quotient.mk m r) x

private theorem mul_eq_mul_of_ratio_eq_one {n : ℕ} {R : Type} [CommRing R] [Algebra k R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → R)
    (he : ∀ I J, e I * e J = if I = J then e I else 0) (hs : ∑ i, e i = 1)
    (φ : ∀ i, LinearMap.range (ρ (e i)) ≃ₗ[k] LinearMap.range (ρ' (e i))) (v : Fin n → k) :
    (∑ i, (LinearMap.range (ρ (e i))).subtype ∘ₗ (φ i).symm.toLinearMap ∘ₗ (ρ' (e i)).rangeRestrict)
      ((∑ i, (LinearMap.range (ρ' (e i))).subtype ∘ₗ (φ i).toLinearMap ∘ₗ (ρ (e i)).rangeRestrict) v) = v := by
  have inner : ∀ i j, (((φ j).symm ((ρ' (e j)).rangeRestrict
      ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)) :
        LinearMap.range (ρ (e j))) : Fin n → k) = if i = j then ρ (e i) v else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      have h1 : (ρ' (e i)).rangeRestrict ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)
          = φ i ((ρ (e i)).rangeRestrict v) := by
        apply Subtype.ext
        have := proj_of_mem ρ' e he i i _ (φ i ((ρ (e i)).rangeRestrict v)).2
        simpa using this
      rw [h1, LinearEquiv.symm_apply_apply, if_pos rfl]
      rfl
    · have h1 : (ρ' (e j)).rangeRestrict ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)
          = 0 := by
        apply Subtype.ext
        have := proj_of_mem ρ' e he i j _ (φ i ((ρ (e i)).rangeRestrict v)).2
        simpa [h] using this
      rw [h1, map_zero, if_neg h]
      rfl
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.coe_subtype,
    LinearEquiv.coe_coe]
  simp only [Submodule.coe_sum, inner]
  simp
  rw [← LinearMap.sum_apply, ← map_sum, hs, map_one]
  rfl

theorem isoOfTrace : IsoOfTrace k := by
  unfold IsoOfTrace
  intro n R _ _ _ _ ρ ρ' htr
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let E := IsArtinianRing.equivPi R
  let e : MaximalSpectrum R → R := fun m => E.symm (Pi.single m 1)
  have hE : ∀ m, E (e m) = Pi.single m 1 := fun m => E.apply_symm_apply _
  have he : ∀ I J, e I * e J = if I = J then e I else 0 := by
    intro I J
    apply E.injective
    rw [map_mul, hE, hE]
    by_cases h : I = J
    · subst h
      rw [if_pos rfl, hE, ← Pi.single_mul, mul_one]
    · rw [if_neg h, map_zero]
      funext x
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hx : x = I
      · subst hx
        rw [Pi.single_eq_of_ne h, mul_zero]
      · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hs : ∑ m, e m = 1 := by
    apply E.injective
    rw [map_sum, map_one]
    funext x
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hm : ∀ m : MaximalSpectrum R, ∀ a ∈ m.asIdeal, a * e m = 0 := by
    intro m a ha
    apply E.injective
    rw [map_mul, hE, map_zero]
    funext x
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases h : x = m
    · subst h
      have h0 : E a x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      rw [h0, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hc : ∀ m : MaximalSpectrum R, ∃ φ : LinearMap.range (ρ (e m)) ≃ₗ[k] LinearMap.range (ρ' (e m)),
      ∀ r x, φ (resHom ρ (e m) r x) = resHom ρ' (e m) r (φ x) := fun m => by
    haveI := m.isMaximal
    exact comp_lemma ρ ρ' (e m) (by simpa using he m m) m.asIdeal (hm m) (htr _)
  choose φ hφ using hc
  let Φ : (Fin n → k) →ₗ[k] (Fin n → k) :=
    ∑ i, (LinearMap.range (ρ' (e i))).subtype ∘ₗ (φ i).toLinearMap ∘ₗ (ρ (e i)).rangeRestrict
  let Ψ : (Fin n → k) →ₗ[k] (Fin n → k) :=
    ∑ i, (LinearMap.range (ρ (e i))).subtype ∘ₗ (φ i).symm.toLinearMap ∘ₗ (ρ' (e i)).rangeRestrict
  have h1 : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext fun v => mul_eq_mul_of_ratio_eq_one ρ ρ' e he hs φ v
  have h2 : Φ ∘ₗ Ψ = LinearMap.id :=
    LinearMap.ext fun v => mul_eq_mul_of_ratio_eq_one ρ' ρ e he hs (fun i => (φ i).symm) v
  refine ⟨LinearEquiv.ofLinear Φ Ψ h2 h1, fun r v => ?_⟩
  show Φ (ρ r v) = ρ' r (Φ v)
  simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.coe_subtype,
    LinearEquiv.coe_coe]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (ρ (e i)).rangeRestrict (ρ r v) = resHom ρ (e i) r ((ρ (e i)).rangeRestrict v) := by
    apply Subtype.ext
    rw [resHom_apply]
    show ρ (e i) (ρ r v) = ρ r (ρ (e i) v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  rw [h3, hφ, resHom_apply]

end PositivityTheory.RgUd.T.Alg.Iso2
