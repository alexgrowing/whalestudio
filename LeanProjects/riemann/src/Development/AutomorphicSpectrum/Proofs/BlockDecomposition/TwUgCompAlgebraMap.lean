import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwUg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem twUg_map (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) :
    (twUg σ B).comp (PAlg.mapUg (PAlg.twMap σ f)) = (PAlg.mapUg f).comp (twUg σ A) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (l : (PAlg.tw σ A).U)) (RingHom.ext fun x => ?_)
  change twUg σ B (PAlg.mapUg (PAlg.twMap σ f) (algebraMap _ _ x)) = PAlg.mapUg f (twUg σ A (algebraMap _ _ x))
  rw [PAlg.mapUg_algebraMap, twUg_algebraMap, twUg_algebraMap, PAlg.mapUg_algebraMap, PAlg.twU_mapU]

theorem twUg_cToUg (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : ℂ_[l]) :
    twUg σ A ((PAlg.tw σ A).cToUg x) = A.cToUg (galCp σ x) := by
  have h : ((twUg σ A).comp (PAlg.tw σ A).cToUg).comp
        ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) =
      (A.cToUg.comp (galCp σ : ℂ_[l] →+* ℂ_[l])).comp ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : OC l)) (RingHom.ext fun y => ?_)
    have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y) = (y : ℂ_[l]) :=
      (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).commutes y
    have e2 : ((galOC σ y : OC l) : ℂ_[l]) = galCp σ (y : ℂ_[l]) := rfl
    change twUg σ A ((PAlg.tw σ A).cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))) =
      A.cToUg (galCp σ ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y)))
    rw [e, PAlg.cToUg_coe, twUg_algebraMap, PAlg.twU_oC, ← e2, PAlg.cToUg_coe]
  obtain ⟨y, rfl⟩ := (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).surjective x
  exact RingHom.congr_fun h y

theorem twUg_kb (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : PadicAlgCl l) :
    twUg σ A (kb (PAlg.tw σ A) x) = kb A (σ x) := by
  change twUg σ A ((PAlg.tw σ A).cToUg (clToC l x)) = A.cToUg (clToC l (σ x))
  rw [twUg_cToUg]
  exact congrArg A.cToUg (galCp_coe σ x)

theorem twUg_comp_algebraMap (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ((twUg σ A).comp (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug)).comp (PAlg.twUEquiv σ A).symm.toRingHom =
      algebraMap A.U A.Ug := by
  refine RingHom.ext fun x => ?_
  change twUg σ A (algebraMap _ _ ((PAlg.twUEquiv σ A).symm x)) = algebraMap A.U A.Ug x
  rw [twUg_algebraMap]
  exact congrArg (algebraMap A.U A.Ug) ((PAlg.twUEquiv σ A).apply_symm_apply x)

theorem geomPt_galMap (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ =
      Spec.map (CommRingCat.ofHom (twUg σ A)) ≫
        geomPt M (PAlg.tw σ A) ((pxTw M.p (okToOC l K) σ (galOC_okToOC σ)).app A y) := by
  refine gb_ext M ?_ ?_
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst_assoc, geomPt_fst, geomPt_fst]
    change _ = _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (PAlg.twUEquiv σ A).symm.toRingHom) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, twUg_comp_algebraMap]
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, geomPt_snd, ← Category.assoc, geomPt_snd,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext fun x => twUg_kb σ A x).symm

end GlobalTheory.CompanionTheory.TwUg

theorem GlobalTheory.CompanionTheory.TwUg.twUg_prop : CrystallineSemistableComparison.E.TwUg := fun _ _ _ σ =>
  ⟨fun _ _ f => GlobalTheory.CompanionTheory.TwUg.twUg_map σ f, fun A x => GlobalTheory.CompanionTheory.TwUg.twUg_kb σ A x,
    fun M A y => GlobalTheory.CompanionTheory.TwUg.geomPt_galMap M σ A y⟩
