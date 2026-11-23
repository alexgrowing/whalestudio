import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MonoEpiPf

variable {R : Type} [CommRing R]

theorem sep {F : Shv R} {U : Scheme.{0}} (a : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = 0) : a = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  have key := Presheaf.IsSheaf.hom_ext F.property ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a)) 0 (by
      intro I
      ext
      have := hP _ I.f I.hf
      simp only [Sec.res] at this
      simp [LinearMap.toSpanSingleton_apply, this])
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) key
  simpa using this

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
    have : Mono (φ.hom.app (op U)) := (NatTrans.mono_iff_mono_app _).1 this _
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      induction U using Opposite.rec with | op U => ?_
      exact (ModuleCat.mono_iff_injective _).2 (h U)
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; simp [Sec.map])
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => by simp [Sec.res]⟩
  · intro h U
    have hk : ∀ a : Sec F U, Sec.map φ a = 0 → a = 0 := fun a ha => sep a (h U a ha)
    intro a b hab
    have : Sec.map φ (a - b) = 0 := by simp only [Sec.map] at hab ⊢; rw [map_sub, hab, sub_self]
    exact sub_eq_zero.1 (hk _ this)

theorem epi_iff {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} R))]
  constructor
  · intro h U b
    refine ⟨Presheaf.imageSieve φ.hom b, h.imageSieve_mem b, fun V g hg => ?_⟩
    rw [Presheaf.imageSieve_apply] at hg
    exact hg
  · intro h
    refine ⟨fun {U} b => ?_⟩
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    rw [Presheaf.imageSieve_apply]
    exact hP V g hg

theorem ext_sec {F G : Shv R} (φ ψ : F ⟶ G)
    (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  induction U using Opposite.rec with | op U => ?_
  exact h U a

end LateralTheory.EtaleFoundations.MonoEpiPf

open LateralTheory.EtaleFoundations.MonoEpiPf in
theorem LateralTheory.EtaleFoundations.etale_sheaf_mono_epi_iff_sections_of_separation : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff φ,
    fun ψ h => ext_sec φ ψ h⟩
