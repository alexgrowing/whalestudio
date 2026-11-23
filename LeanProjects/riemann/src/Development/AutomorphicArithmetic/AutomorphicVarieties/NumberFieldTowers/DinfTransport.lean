import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.PlaceTransport

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem dt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'} {A : ValuationSubring Ω}
    {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

private theorem dt_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Dec (F := F') A') :
    g ∈ Dec (F := F) A := by
  have h' : ∀ x, σ (g⁻¹ x) = g'⁻¹ (σ x) := fun x => by
    show σ (g.symm x) = g'.symm (σ x)
    rw [eq_comm, AlgEquiv.symm_apply_eq, ← h, AlgEquiv.apply_symm_apply]
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hA, hA, h']
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _

private theorem dt_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A')
    {g : G F Ω} {g' : G F' Ω'} (h : ∀ x, σ (g x) = g' (σ x)) (hg : g' ∈ Ine (F := F') A') :
    g ∈ Ine (F := F) A := by
  refine ⟨dt_dec hA h hg.1, fun x hx => ?_⟩
  rw [dt_val_lt_one hA, map_sub, h]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))

private theorem dt_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] (σ : Ω ≃+* Ω') (N : ℕ)
    {V : Subgroup (G F Ω)} {V' : Subgroup (G F' Ω')} (e : V' →* V) (he : Continuous e)
    (h : ∀ (u : V') x, σ ((e u).1 x) = u.1 (σ x)) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {ψ : V → M} (hψ : ψ ∈ XDual N V R M) : ψ ∘ e ∈ XDual N V' R M := by
  have hA : ∀ (A' : ValuationSubring Ω') x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun _ _ => Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := hψ
  refine ⟨h1.comp_continuous he, fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
  · simp only [Function.comp_apply, map_mul, h2]
  · exact h3 (A.comap σ.toRingHom) _ (dt_ine (hA A) (h u) hu)
  · refine h4 (A.comap σ.toRingHom) ?_ _ (dt_dec (hA A) (h u) hu)
    rw [dt_val_lt_one (hA A), map_natCast]
    exact hN

theorem UpperTheory.V.Tower.dinfTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
        ∀ φ : G F' Ω' →* G F Ω, (∀ g x, σ (φ g x) = g (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) (U' : Subgroup (G F' Ω')),
          (cycU l U').map φ = cycU l U → ∃ Ψ : Dinf l N U ≃ₗ[ℤ_[l]] Dinf l N U', ∀ (ψ : Dinf l N U) (u' : cycU l U') (u : cycU l U), u.1 = φ u'.1 → (Ψ ψ).1 u' = ψ.1 u := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ f σ h φ hφ l _ N U U' hU
  obtain ⟨φ₀, hc, hφ₀, -, hi, -⟩ := galTransport F Ω F' Ω' f σ h
  obtain rfl : φ₀ = φ := MonoidHom.ext fun g => AlgEquiv.ext fun x => σ.injective (by rw [hφ, hφ₀])
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : IsGalois F' Ω' := IsAlgClosure.isGalois F' Ω'
  have hemb : Topology.IsInducing φ₀ := (hc.isClosedEmbedding hi).isInducing
  let e : cycU l U' ≃* cycU l U := ((cycU l U').equivMapOfInjective φ₀ hi).trans (MulEquiv.subgroupCongr hU)
  have he : ∀ u, (e u).1 = φ₀ u.1 := fun _ => rfl
  have he' : ∀ u, φ₀ (e.symm u).1 = u.1 := fun u => by rw [← he, MulEquiv.apply_symm_apply]
  have c1 : Continuous e.toMonoidHom := (hc.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e.symm.toMonoidHom := by
    refine continuous_induced_rng.2 (hemb.continuous_iff.2 ?_)
    exact continuous_subtype_val.congr fun u => (he' u).symm
  refine ⟨{ toFun := fun ψ => ⟨ψ.1 ∘ e.toMonoidHom, dt_mem σ N e.toMonoidHom c1 (fun u x => hφ u.1 x) ψ.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun ψ => ⟨ψ.1 ∘ e.symm.toMonoidHom, dt_mem σ.symm N e.symm.toMonoidHom c2 (fun u x => ?_) ψ.2⟩
            left_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.apply_symm_apply u))
            right_inv := fun ψ => Subtype.ext (funext fun u => congrArg ψ.1 (e.symm_apply_apply u)) }, ?_⟩
  · show σ.symm ((e.symm u).1 x) = u.1 (σ.symm x)
    rw [RingEquiv.symm_apply_eq, ← he' u, hφ, RingEquiv.apply_symm_apply]
  · intro ψ u' u hu
    exact congrArg ψ.1 (Subtype.ext hu.symm)
