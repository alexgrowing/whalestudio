import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

namespace GlobalTheory.CompanionTheory.GSCd.Transport

section Places

variable {R R' : Type*} [CommRing R] [CommRing R']

def placeMap (f : R ≃+* R') (v : HeightOneSpectrum R) : HeightOneSpectrum R' where
  asIdeal := v.asIdeal.comap f.symm
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply v.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : f x ∈ v.asIdeal.comap f.symm := by simpa [Ideal.mem_comap] using hx
    rw [h] at h1
    have h0 : f x = 0 := (Ideal.mem_bot).1 h1
    exact (Ideal.mem_bot).2 ((map_eq_zero_iff f f.injective).1 h0)

def placeEquiv (f : R ≃+* R') : HeightOneSpectrum R ≃ HeightOneSpectrum R' where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv v := HeightOneSpectrum.ext (by
    ext x
    change f.symm (f x) ∈ v.asIdeal ↔ _
    simp)
  right_inv v := HeightOneSpectrum.ext (by
    ext x
    change f (f.symm x) ∈ v.asIdeal ↔ _
    simp)

end Places

theorem isUnramifiedIn_transport {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A]
    [CommRing A'] [Algebra R A] [Algebra R' A'] (f : R ≃+* R') (g : A ≃+* A')
    (h : ∀ r, g (algebraMap R A r) = algebraMap R' A' (f r)) (p : Ideal R)
    (H : Algebra.IsUnramifiedIn A p) : Algebra.IsUnramifiedIn A' (p.comap f.symm) := by
  intro P' hP' hlie
  let P : Ideal A := P'.comap g
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.LiesOver p := ⟨by
    ext r
    have h1 := hlie.over
    have h2 : f r ∈ p.comap f.symm ↔ f r ∈ P'.under R' := by rw [← h1]
    simp only [Ideal.mem_comap, RingEquiv.symm_apply_apply] at h2
    rw [h2, Ideal.under_def]
    change _ ↔ g (algebraMap R A r) ∈ P'
    rw [h]⟩
  have hU : Algebra.FormallyUnramified R (Localization.AtPrime P) := H P this hP
  letI : Algebra R R' := f.toRingHom.toAlgebra
  letI : Algebra R (Localization.AtPrime P') :=
    ((algebraMap R' (Localization.AtPrime P')).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower R R' (Localization.AtPrime P') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hM : Submonoid.map g.toMonoidHom P.primeCompl = P'.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨g.symm y, ?_, by simp⟩
      intro hmem
      apply hy
      simpa [P, Ideal.mem_comap] using hmem
  let E : Localization.AtPrime P ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P) (Localization.AtPrime P') g hM
  let Ea : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime P' :=
    AlgEquiv.ofRingEquiv (f := E) (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime P)]
      simp only [E]
      rw [IsLocalization.ringEquivOfRingEquiv_eq, h]
      exact (IsScalarTower.algebraMap_apply R' A' (Localization.AtPrime P') (f r)).symm)
  haveI := Algebra.FormallyUnramified.of_equiv Ea
  exact Algebra.FormallyUnramified.of_restrictScalars R R' _

section Fields

variable {F F' Ω Ω' : Type*} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω]
  [Algebra F' Ω']

def resEquiv (e : Ω ≃+* Ω') (E : IntermediateField F Ω) (E' : IntermediateField F' Ω')
    (h : ∀ x, x ∈ E ↔ e x ∈ E') : E ≃+* E' where
  toFun x := ⟨e x, (h x).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simpa using y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def tr (ψ : F ≃+* F') (e : Ω ≃+* Ω') (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    (E : IntermediateField F Ω) : IntermediateField F' Ω' :=
  Subfield.toIntermediateField (E.toSubfield.comap e.symm.toRingHom) (fun x => by
    have h1 : e.symm (algebraMap F' Ω' x) = algebraMap F Ω (ψ.symm x) := by
      rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]
    change e.symm (algebraMap F' Ω' x) ∈ E
    rw [h1]
    exact E.algebraMap_mem _)

theorem mem_tr (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω) (x : Ω) :
    x ∈ E ↔ e x ∈ tr ψ e he E := by
  change _ ↔ e.symm (e x) ∈ E
  simp

theorem resEquiv_algebraMap (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω') (h : ∀ x, x ∈ E ↔ e x ∈ E') (x : F) :
    resEquiv e E E' h (algebraMap F E x) = algebraMap F' E' (ψ x) :=
  Subtype.ext (he x)

theorem finite_of_resEquiv (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω') (h : ∀ x, x ∈ E ↔ e x ∈ E') [FiniteDimensional F E] :
    FiniteDimensional F' E' :=
  Module.Finite.of_equiv_equiv ψ (resEquiv e E E' h) (by
    ext x
    exact (congrArg Subtype.val (resEquiv_algebraMap ψ e he E E' h x)).symm)

end Fields

section Galois

variable {F F' L L' : Type*} [Field F] [Field F'] [Field L] [Field L'] [Algebra F L]
  [Algebra F' L']

theorem symm_compat (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (x : F') :
    e.symm (algebraMap F' L' x) = algebraMap F L (ψ.symm x) := by
  rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]

def galMap (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (σ : Gal(L/F)) : Gal(L'/F') :=
  AlgEquiv.ofRingEquiv (f := (e.symm.trans σ.toRingEquiv).trans e) (fun x => by
    change e (σ (e.symm (algebraMap F' L' x))) = _
    rw [symm_compat ψ e he, σ.commutes, he, RingEquiv.apply_symm_apply])

theorem galMap_apply (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (σ : Gal(L/F)) (y : L') :
    galMap ψ e he σ y = e (σ (e.symm y)) := rfl

def galEquiv (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) : Gal(L/F) ≃* Gal(L'/F') where
  toFun := galMap ψ e he
  invFun := galMap ψ.symm e.symm (symm_compat ψ e he)
  left_inv σ := AlgEquiv.ext fun x => by simp [galMap_apply]
  right_inv σ := AlgEquiv.ext fun x => by simp [galMap_apply]
  map_mul' σ τ := AlgEquiv.ext fun x => by simp [galMap_apply]

theorem continuous_galEquiv (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) :
    Continuous (galEquiv ψ e he) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E', hE', hs⟩ := hs
  let E : IntermediateField F L := tr ψ.symm e.symm (symm_compat ψ e he) E'
  have hmem : ∀ x, x ∈ E ↔ e x ∈ E' := fun x => by
    change e.symm.symm x ∈ E' ↔ _
    rfl
  have hmem' : ∀ y, y ∈ E' ↔ e.symm y ∈ E := mem_tr ψ.symm e.symm (symm_compat ψ e he) E'
  have hfin : FiniteDimensional F E :=
    finite_of_resEquiv ψ.symm e.symm (symm_compat ψ e he) E' E hmem'
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((IntermediateField.fixingSubgroup_isOpen E).mem_nhds
    (Subgroup.one_mem _)) fun σ hσ => hs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ (e.symm y) ((hmem' y).1 hy)
  change e (σ (e.symm y)) = y
  rw [h1, RingEquiv.apply_symm_apply]

def galHomeo (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) : Gal(L/F) ≃ₜ* Gal(L'/F') :=
  { galEquiv ψ e he with
    continuous_toFun := continuous_galEquiv ψ e he
    continuous_invFun := continuous_galEquiv ψ.symm e.symm (symm_compat ψ e he) }

end Galois

section NumberFields

variable {F F' Ω Ω' : Type*} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω]
  [Algebra F' Ω']

theorem placeEquiv_symm_map (ψ : F ≃+* F') :
    placeEquiv (RingOfIntegers.mapRingEquiv ψ.symm) =
      (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm := rfl

def Corr (ψ : F ≃+* F') (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) :
    Prop :=
  ∀ v, v ∈ S ↔ placeEquiv (RingOfIntegers.mapRingEquiv ψ) v ∈ S'

theorem Corr.symm {ψ : F ≃+* F'} {S : Set (HeightOneSpectrum (𝓞 F))}
    {S' : Set (HeightOneSpectrum (𝓞 F'))} (h : Corr ψ S S') : Corr ψ.symm S' S := by
  intro w
  rw [placeEquiv_symm_map, h, Equiv.apply_symm_apply]

theorem unram_tr (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} {S' : Set (HeightOneSpectrum (𝓞 F'))} (hS : Corr ψ S S')
    {E : IntermediateField F Ω} (hE : IsUnramifiedOutside S E) :
    IsUnramifiedOutside S' (tr ψ e he E) := by
  intro w hw
  set f := RingOfIntegers.mapRingEquiv ψ with hf
  set v := (placeEquiv f).symm w with hv
  have hvS : v ∉ S := fun h => hw (by
    have h2 : placeEquiv f v ∈ S' := (hS v).1 h
    rwa [hv, Equiv.apply_symm_apply] at h2)
  have hcompat : ∀ r : 𝓞 F, RingOfIntegers.mapRingEquiv (resEquiv e E (tr ψ e he E) (mem_tr ψ e he E))
      (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap (𝓞 F') (𝓞 (tr ψ e he E)) (f r) := fun r =>
    Subtype.ext (Subtype.ext (he (r : F)))
  have h1 := isUnramifiedIn_transport f _ hcompat v.asIdeal (hE v hvS)
  have hw' : v.asIdeal.comap f.symm = w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal ((placeEquiv f).apply_symm_apply w)
  rwa [hw'] at h1

variable [NumberField F] [NumberField F'] [IsGalois F Ω] [IsGalois F' Ω']

theorem mem_max (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} {S' : Set (HeightOneSpectrum (𝓞 F'))} (hS : Corr ψ S S')
    {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) : e x ∈ maxUnramifiedOutside F' Ω' S' := by
  obtain ⟨E, hf, hu, hxE⟩ := (mem_maxUnramifiedOutside_iff S).1 hx
  exact (mem_maxUnramifiedOutside_iff S').2 ⟨tr ψ e he E,
    finite_of_resEquiv ψ e he E _ (mem_tr ψ e he E), unram_tr ψ e he hS hu,
    (mem_tr ψ e he E x).1 hxE⟩

theorem nonempty_gal (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} {S' : Set (HeightOneSpectrum (𝓞 F'))} (hS : Corr ψ S S') :
    Nonempty (galUnramifiedOutside F Ω S ≃ₜ* galUnramifiedOutside F' Ω' S') := by
  have hiff : ∀ x, x ∈ maxUnramifiedOutside F Ω S ↔ e x ∈ maxUnramifiedOutside F' Ω' S' := fun x =>
    ⟨mem_max ψ e he hS, fun h => by
      simpa using mem_max ψ.symm e.symm (symm_compat ψ e he) hS.symm h⟩
  exact ⟨galHomeo ψ (resEquiv e _ _ hiff)
    (resEquiv_algebraMap ψ e he _ _ hiff)⟩

end NumberFields

theorem exists_embedded (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] : ∃ (K : FiniteSubfield) (ψ : F ≃+* K.1) (e : Ω ≃+* AlgebraicClosure ℚ),
      ∀ x, e (algebraMap F Ω x) = algebraMap K.1 (AlgebraicClosure ℚ) (ψ x) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  let e : Ω ≃ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosure.equiv ℚ (AlgebraicClosure ℚ) Ω |>.symm
  let φ : F →ₐ[ℚ] AlgebraicClosure ℚ := e.toAlgHom.comp (IsScalarTower.toAlgHom ℚ F Ω)
  let ψ0 : F →+* φ.fieldRange :=
    { toFun := fun x => ⟨φ x, x, rfl⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y) }
  let ψ : F ≃+* φ.fieldRange := RingEquiv.ofBijective ψ0
    ⟨ψ0.injective, fun y => by
      obtain ⟨y, x, rfl⟩ := y
      exact ⟨x, rfl⟩⟩
  have hfin : FiniteDimensional ℚ φ.fieldRange :=
    Module.Finite.of_equiv_equiv (RingEquiv.refl ℚ) ψ (Subsingleton.elim _ _)
  exact ⟨⟨φ.fieldRange, hfin⟩, ψ, e.toRingEquiv, fun _ => rfl⟩

theorem exists_gs_transport : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧ Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* Gs K S') := by
  intro F Ω _ _ _ _ _ l S hS
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨K, ψ, e, he⟩ := exists_embedded F Ω
  classical
  refine ⟨K, S.map (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding, ?_,
    nonempty_gal ψ e he ?_⟩
  · intro w hw
    have hv : (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S := by
      apply hS
      change RingOfIntegers.mapRingEquiv ψ (l : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_map.2 ⟨_, hv, (placeEquiv _).apply_symm_apply w⟩
  · intro v
    simp

end GlobalTheory.CompanionTheory.GSCd.Transport
