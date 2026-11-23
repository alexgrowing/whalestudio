import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionRepresentingRelativeClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCupProductHomOfCocycleVanishingOnOpen
import Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductRealizesProductOfRepresentativ
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveIffTotalQuasiIsoOfTotalModels
import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexBotTotalModel
import Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCohomologyIsTotalModelOfImage
import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexIsAdmissible
import Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCupProductLevelwiseCompat
import Development.AutomorphicArithmetic.CommutativeAlgebra.TotalExactOfColumnExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem key (aw : LeafAW) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc}
    (π : E ⟶ sch.obj X) (m j i : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X)
    (hβ : IsRep U β c.1)
    (Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom
      (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m))
    (hP : IsProd (twPair q i j) π β Φ) (hO : Φ.Ok) :
    (∀ n : ℤ, Function.Bijective fun a : Ht q E n i =>
      Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)) ↔ Φ.TotEx := by
  exact UpperTheory.bijective_iff_totalQuasiIso_of_totalModels _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO
    (fun n => Ht q E n i) (fun n => ↥(Hs q (abv U π) (n + m) (i + j)))
    (fun n x a => HRel x a) (fun n x b => SRel x (b : Ht q (dbl (abv U π)) (n + m) (i + j)))
    (fun n a => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c))
    (fun n => UpperTheory.supportDoubleComplex_bot_totalModel _ _ _ n) (fun n => UpperTheory.relativeCohomology_isTotalModel_of_image q (abv U π) (i + j) m n (n + m) rfl)
    (fun n x a h => UpperTheory.relativeCupProduct_realizes_product_of_representative aw q U π m j i n c β hβ Φ hP x a h)

theorem UpperTheory.productLevelwise_of_alexanderWhitney :
    LeafAW → LeafPrdLevel := by
  intro aw _ q _ X U E π m j c hlev n i
  obtain ⟨β, hβ⟩ := UpperTheory.exists_section_representing_relativeClass q X U m j c
  obtain ⟨Φ, hP, hO⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U π m β hβ.1 hβ.2.1
  have hT : Φ.TotEx := by
    refine UpperTheory.totalExact_of_columnExact _ _ Φ (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) (UpperTheory.supportDoubleComplex_isAdmissible _ _ _ _ _) hO ?_
    intro p
    obtain ⟨Ψ, hPΨ, hOΨ⟩ := UpperTheory.exists_cupProduct_hom_of_cocycle_vanishing_on_open _ (twPair q i j) U
      (disc.map (π.app (op { len := p }))) m β hβ.1 hβ.2.1
    refine UpperTheory.relativeCupProduct_levelwise_compat _ (twPair q i j) U π m β p Φ Ψ hP hPΨ ?_
    exact (key aw q U (disc.map (π.app (op { len := p }))) m j i c β hβ Ψ hPΨ hOΨ).1
      (fun n' => hlev (op { len := p }) n' i)
  exact (key aw q U π m j i c β hβ Φ hP hO).2 hT n
