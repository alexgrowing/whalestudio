import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.PostFun

variable {R : Type} [CommRing R]

theorem post_eq_cpush (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    HK.post R K φ n = cpush K (resMap R φ) n := rfl

def resMapIdHomotopy (F : Shv R) : Homotopy (resMap R (𝟙 F)) (𝟙 (res R F)) := by
  have H2 := (InjectiveResolution.descIdHomotopy F (injectiveResolution F)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_id] at H2
  exact H2

def resMapCompHomotopy {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) :
    Homotopy (resMap R (φ ≫ ψ)) (resMap R φ ≫ resMap R ψ) := by
  have H2 := (InjectiveResolution.descCompHomotopy φ ψ (injectiveResolution F) (injectiveResolution G)
    (injectiveResolution M)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp] at H2
  exact H2

def resMapAddHomotopy {F G : Shv R} (φ ψ : F ⟶ G) :
    Homotopy (resMap R (φ + ψ)) (resMap R φ + resMap R ψ) := by
  have H : Homotopy (InjectiveResolution.desc (φ + ψ) (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
        InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F)) := by
    apply InjectiveResolution.descHomotopy (φ + ψ)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp, Functor.map_add]
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_add] at H2
  exact H2

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
  rw [← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapIdHomotopy F), InjResCmp.cpush_id]

theorem post_comp (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapCompHomotopy φ ψ), InjResCmp.cpush_comp]
  rfl

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) :
    HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n := by
  ext x
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapAddHomotopy φ ψ), cpush_add]
  rfl

def postHom (K : Cx R) (F G : Shv R) (n : ℤ) : (F ⟶ G) →+ (HK R K F n →+ HK R K G n) :=
  AddMonoidHom.mk' (fun φ => HK.post R K φ n) (fun φ ψ => post_add K φ ψ n)

theorem post_zsmul (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (c : ℤ) (n : ℤ) (x : HK R K F n) :
    HK.post R K (c • φ) n x = c • HK.post R K φ n x := by
  have h := map_zsmul (postHom K F G n) c φ
  exact DFunLike.congr_fun h x

theorem pull_post {K L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) :=
  ZcFun.cpull_cpush f (resMap R φ) n x

theorem main : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  intro R _ K n
  exact ⟨fun F x => post_id K F n x, fun φ ψ x => post_comp K φ ψ n x, fun φ ψ => post_add K φ ψ n,
    fun φ c x => post_zsmul K φ c n x, fun f _ _ φ x => pull_post f φ n x⟩

end GlobalTheory.EtC.PostFun
