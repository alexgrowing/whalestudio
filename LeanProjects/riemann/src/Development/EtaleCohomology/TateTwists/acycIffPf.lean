import Development.EtaleCohomology.TateTwists.acycPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.acycIffPf

variable {R : Type} [CommRing R]

abbrev ev (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem app_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem iCycles_inj (S : ShortComplex (Shv R)) (U : Scheme.{0}) :
    Function.Injective (Sec.map S.iCycles (U := U)) := by
  have : Mono ((ev U).map S.iCycles) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem iCycles_surj (S : ShortComplex (Shv R)) (U : Scheme.{0}) (z : Sec S.X₂ U) (hz : Sec.map S.g z = 0) :
    ∃ c : Sec S.cycles U, Sec.map S.iCycles c = z := by
  let S' : ShortComplex (Shv R) := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hS' : S'.Exact := S'.exact_of_f_is_kernel S.cyclesIsKernel
  have hE : (S'.map (ev U)).Exact := hS'.map_of_mono_of_preservesKernel (ev U) (inferInstanceAs (Mono S.iCycles)) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hE z hz

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔
    ∀ (U : Scheme.{0}) (z : Sec S.X₂ U), Sec.map S.g z = 0 →
      Loc U fun V g => ∃ y : Sec S.X₁ V, Sec.map S.f y = Sec.res g z := by
  rw [S.exact_iff_epi_toCycles, ← Sheaf.isLocallySurjective_iff_epi' _ S.toCycles]
  constructor
  · intro h U z hz
    obtain ⟨c, rfl⟩ := iCycles_surj S U z hz
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} S.toCycles.hom (U := op U) c, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : Sec.map S.f t = Sec.map S.iCycles (Sec.map S.toCycles t) := by
      rw [← app_comp, S.toCycles_i]
    rw [h1, ← map_res]
    exact congrArg _ ht
  · intro h
    constructor
    intro U c
    obtain ⟨Sv, hSv, hP⟩ := h U (Sec.map S.iCycles c) (by rw [← app_comp, S.iCycles_g]; rfl)
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hSv
    intro V g hg
    obtain ⟨y, hy⟩ := hP V g hg
    refine ⟨y, iCycles_inj S V ?_⟩
    change Sec.map S.iCycles (Sec.map S.toCycles y) = Sec.map S.iCycles (Sec.res g c)
    rw [← app_comp, S.toCycles_i, hy, map_res]

end LateralTheory.EtaleFoundations.acycIffPf

open LateralTheory.EtaleFoundations.acycIffPf in
theorem LateralTheory.EtaleFoundations.acyc.acycIff_of : LateralTheory.EtaleFoundations.acyc.acycIff := by
  intro R _ C
  unfold LateralTheory.EtaleFoundations.acyc.LocAcyc
  constructor
  · intro h U n z hz
    have := (HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)).1 (h n)
    exact (exact_iff _).1 this U z hz
  · intro h n
    rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)]
    exact (exact_iff _).2 fun U z hz => h U n z hz
