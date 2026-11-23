import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exactIff_loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem exactIff_map_comp {R : Type} [CommRing R] {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem exactIff_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun m => m.hom x) (φ.hom.naturality g.op)
  simpa using this

theorem exactIff_kernel_sec {R : Type} [CommRing R] {G K : Shv R} (ψ : G ⟶ K) {U : Scheme.{0}}
    (b : Sec G U) (hb : Sec.map ψ b = 0) : ∃ k : Sec (kernel ψ) U, Sec.map (kernel.ι ψ) k = b := by
  let Φ : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
    sheafToPresheaf Scheme.etaleTopology _ ⋙ (evaluation _ _).obj (op U)
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel ψ)
  have hTm : Mono T.f := inferInstanceAs (Mono (kernel.ι ψ))
  have hP : PreservesLimit (parallelPair T.g 0) Φ := inferInstanceAs (PreservesLimit (parallelPair ψ 0) Φ)
  have h2 := (ShortComplex.moduleCat_exact_iff _).1 (hT.map_of_mono_of_preservesKernel Φ hTm hP) b hb
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, hk⟩

theorem exactIff : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  intro R _ S
  have hME : ∀ {F G : Shv R} (φ : F ⟶ G), _ := fun {F G} φ => GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R φ
  rw [ShortComplex.exact_iff_epi_kernel_lift, (hME (kernel.lift S.g S.f S.zero)).2.2.1]
  have hinj : ∀ U, Function.Injective (Sec.map (kernel.ι S.g) (U := U)) :=
    ((hME (kernel.ι S.g)).1).1 inferInstance
  have hfac : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := fun a => by
    rw [← exactIff_map_comp, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := exactIff_kernel_sec S.g b hb
    refine exactIff_loc_mono (h U k) fun V g ⟨a, ha⟩ => ⟨a, ?_⟩
    rw [← hfac, ha, exactIff_map_res]
  · intro h U k
    have hk : Sec.map S.g (Sec.map (kernel.ι S.g) k) = 0 := by
      rw [← exactIff_map_comp, kernel.condition]; rfl
    refine exactIff_loc_mono (h U _ hk) fun V g ⟨a, ha⟩ => ⟨a, hinj V ?_⟩
    rw [hfac, ha, exactIff_map_res]

end GlobalTheory.EtC
