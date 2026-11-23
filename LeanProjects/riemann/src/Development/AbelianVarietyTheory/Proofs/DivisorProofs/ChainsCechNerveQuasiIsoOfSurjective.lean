import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsQuasiIsoOfSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
open Simplicial SimplicialObject.Augmented
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtC.CechSplit

variable {P Q : PSh} (φ : P ⟶ Q) (hφ : ∀ U, Function.Surjective (φ.app U)) (U : Scheme.{0})

def lft (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ P :=
  yonedaEquiv.symm (hφ (op U) (yonedaEquiv c)).choose

@[reassoc (attr := simp)]
lemma lft_comp (c : yoneda.obj U ⟶ Q) : lft φ hφ U c ≫ φ = c := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, lft, Equiv.apply_symm_apply]
  exact (hφ (op U) (yonedaEquiv c)).choose_spec

def sf (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (x ≫ WidePullback.base _)
    (Fin.cases (lft φ hφ U (x ≫ WidePullback.base _)) (fun i => x ≫ WidePullback.π _ i))
    (fun i => by cases i using Fin.cases <;> simp)

def sf' (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌) :=
  lft φ hφ U c ≫ WidePullback.lift φ (fun _ => 𝟙 P) (by simp)

lemma sf'_comp_aug (c : yoneda.obj U ⟶ Q) : sf' φ hφ U c ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌) = c := by
  simp [sf']

lemma sf_zero_comp_δ_one (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌)) :
    sf φ hφ U 0 x ≫ (Arrow.mk φ).cechNerve.δ 1 =
      sf' φ hφ U (x ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌)) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf, sf']
  ext j
  · fin_cases j
    simp
  · simp

lemma sf_comp_δ_zero (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.δ 0 = x := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · simp
  · simp

lemma sf_succ_comp_δ_succ (n : ℕ) (i : Fin (n + 2)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌)) :
    sf φ hφ U (n + 1) x ≫ (Arrow.mk φ).cechNerve.δ i.succ = sf φ hφ U n (x ≫ (Arrow.mk φ).cechNerve.δ i) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

lemma sf_comp_σ_succ (n : ℕ) (i : Fin (n + 1)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.σ i.succ = sf φ hφ U (n + 1) (x ≫ (Arrow.mk φ).cechNerve.σ i) := by
  dsimp [SimplicialObject.σ, SimplexCategory.σ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

def ed : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)))).obj
    (Arrow.mk φ).augmentedCechNerve) where
  s' := TypeCat.ofHom (sf' φ hφ U)
  s n := TypeCat.ofHom (sf φ hφ U n)
  s'_comp_ε := by ext c; exact sf'_comp_aug φ hφ U c
  s₀_comp_δ₁ := by ext x; exact sf_zero_comp_δ_one φ hφ U x
  s_comp_δ₀ n := by ext x; exact sf_comp_δ_zero φ hφ U n x
  s_comp_δ n i := by ext x; exact sf_succ_comp_δ_succ φ hφ U n i x
  s_comp_σ n i := by ext x; exact sf_comp_σ_succ φ hφ U n i x

def toConst : (Arrow.mk φ).augmentedCechNerve ⟶ SimplicialObject.Augmented.const.obj Q where
  left := (Arrow.mk φ).augmentedCechNerve.hom
  right := 𝟙 Q
  w := by ext : 1; simp

include hφ in
theorem free_sections_quasiIso (R : Type) [CommRing R] :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
      (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙
        ModuleCat.free (ULift.{1} R))).map
          (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom))) := by
  let G : PSh ⥤ ModuleCat.{1} (ULift.{1} R) :=
    (evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)
  let X := (Arrow.mk φ).augmentedCechNerve
  let e1 : coyoneda.obj (op (yoneda.obj U)) ⋙ ModuleCat.free (ULift.{1} R) ≅ G :=
    Functor.isoWhiskerRight (largeCurriedYonedaLemma.app (op U)) (ModuleCat.free (ULift.{1} R))
  let ed0 : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)) ⋙
      ModuleCat.free (ULift.{1} R))).obj X) := (ed φ hφ U).map (ModuleCat.free (ULift.{1} R))
  let ed1 : ExtraDegeneracy (((whiskering _ _).obj G).obj X) :=
    ed0.ofIso (((whiskering _ _).mapIso e1).app X)
  have h1 := ed1.homotopyEquiv.quasiIso_hom
  have h2 := ((ExtraDegeneracy.const Q).map G).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := ModuleCat.{1} (ULift.{1} R))).naturality
    (((whiskering _ _).obj G).map (toConst φ))
  have hp : (point ⋙ ChainComplex.single₀ _).map (((whiskering _ _).obj G).map (toConst φ)) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map (G.map (𝟙 Q)) = 𝟙 _
    rw [G.map_id, CategoryTheory.Functor.map_id]
  rw [hp, Category.comp_id] at nat
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := h2
  rw [← quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q)))]
  have key : QuasiIso ((drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
        (((whiskering _ _).obj G).map (toConst φ)) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := by
    rw [nat]; exact h1
  exact key

end GlobalTheory.EtC.CechSplit

namespace GlobalTheory.EtC

theorem chains_cechNerve_quasiIso_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q),
    (∀ U, Function.Surjective (φ.app U)) →
      QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
        (Arrow.mk φ).augmentedCechNerve.hom)) := by
  intro R _ P Q φ hφ
  exact chains_quasiIso_of_sections R _ (fun U => CechSplit.free_sections_quasiIso φ hφ U R)

end GlobalTheory.EtC
