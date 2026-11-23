import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelProdIdx
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.PeriodIntegrals.LevelProdIdx

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem levFinIdx_of_prod (h : PI.LevelProdIdx) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤)
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig S.gram (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v)
    (hlev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb)
    (hcof : {v | Uloc v ≠ levelVL hc.sig S.gram v Lb}.Finite)
    (hidx : ∀ v, (Uloc v).relIndex (levelVL hc.sig S.gram v Lb) ≠ 0) :
    Formalism.L2.G.LevFinIdx hc S Lb U :=
  h F E S.rank hc.sig S.gram Lb Uloc U hfin hspan hU hlev hcof hidx

theorem Formalism.L2.G.level_subgroup_finiteIndex (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤)
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig S.gram (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v)
    (hlev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb)
    (hcof : {v | Uloc v ≠ levelVL hc.sig S.gram v Lb}.Finite)
    (hidx : ∀ v, (Uloc v).relIndex (levelVL hc.sig S.gram v Lb) ≠ 0) :
    Formalism.L2.G.LevFinIdx hc S Lb U :=
  levFinIdx_of_prod level_product_index hc S Lb Uloc U hfin hspan hU hlev hcof hidx
