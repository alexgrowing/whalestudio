import Development.EtaleCohomology.CohomologicalPurity.LeafSumPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

variable {R : Type} [CommRing R] {A : Type} {K : A → Cx R} {c : Cofan K}

instance hasColShv : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : IsGrothendieckAbelian.{1} (Shv R) := inferInstance
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

def hcp (hc : IsColimit c) (p : ℤ) : IsColimit ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p).mapCocone c) :=
  haveI : PreservesColimitsOfShape (Discrete A) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p) := inferInstance
  isColimitOfPreserves _ hc

variable {L : Cx R} {n : ℤ}

def glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hcp hc p).desc
    ⟨L.X q, Discrete.natTrans fun j => (y j.as).v p q hpq⟩

theorem glue_v (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) (p q : ℤ) (hpq : p + n = q) :
    (c.inj a).f p ≫ (glue hc y).v p q hpq = (y a).v p q hpq := by
  simp only [glue]
  exact (hcp hc p).fac _ ⟨a⟩

theorem comp_glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) :
    (Cochain.ofHom (c.inj a)).comp (glue hc y) (zero_add n) = y a := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, glue_v]

theorem ext_cochain (hc : IsColimit c) {z₁ z₂ : Cochain c.pt L n}
    (h : ∀ a, (Cochain.ofHom (c.inj a)).comp z₁ (zero_add n) = (Cochain.ofHom (c.inj a)).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine (hcp hc p).hom_ext fun ⟨a⟩ => ?_
  have := congrArg (fun z => z.v p q hpq) (h a)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  exact this

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut
open HKSumPf

theorem LeafHKSum_of : LeafHKSum := by
  intro R _ F A K c hc' n
  obtain ⟨hc⟩ := hc'
  have key : ∀ (a : A) (z : Cocycle c.pt (res R F) n),
      HK.pull R (c.inj a) F n (CohomologyClass.mk z) =
        CohomologyClass.mk (zcomp (Cocycle.ofHom (c.inj a)) z (zero_add n)) := fun _ _ => rfl
  constructor
  · let Φ : HK R c.pt F n →+ (∀ a, HK R (K a) F n) := AddMonoidHom.pi fun a => HK.pull R (c.inj a) F n
    change Function.Injective Φ
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := x.mk_surjective
    have h1 : ∀ a, ∃ β : Cochain (K a) (res R F) (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj a)).comp z.1 (zero_add n) := by
      intro a
      have := congrFun hx a
      change HK.pull R (c.inj a) F n (CohomologyClass.mk z) = 0 at this
      rw [key, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at this
      exact this
    choose β hβ using h1
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨glue hc β, ext_cochain hc fun a => ?_⟩
    rw [← δ_ofHom_comp, comp_glue, hβ]
  · intro f
    have h1 : ∀ a, ∃ z : Cocycle (K a) (res R F) n, CohomologyClass.mk z = f a := fun a => (f a).mk_surjective
    choose z hz using h1
    have hcoc : δ n (n + 1) (glue hc fun a => (z a).1) = 0 := by
      refine ext_cochain hc fun a => ?_
      rw [← δ_ofHom_comp, comp_glue, Cochain.comp_zero]
      exact Cocycle.δ_eq_zero _ _
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hcoc), funext fun a => ?_⟩
    show HK.pull R (c.inj a) F n _ = _
    rw [key, ← hz a]
    congr 1
    exact Cocycle.ext (comp_glue hc _ a)

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
