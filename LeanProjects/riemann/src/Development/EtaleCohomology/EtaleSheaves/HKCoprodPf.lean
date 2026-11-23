import Development.EtaleCohomology.EtaleSheaves.CoprodPf

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.HKCoprodPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {K : ι → CochainComplex C ℤ} (c : Cofan K)
  (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {L : CochainComplex C ℤ}

include hc in
theorem hom_ext_v {p q : ℤ} {a b : c.pt.X p ⟶ L.X q} (h : ∀ j, (c.inj j).f p ≫ a = (c.inj j).f p ≫ b) : a = b :=
  (hc p).hom_ext fun ⟨j⟩ => h j

include hc in
theorem cochain_ext {n : ℤ} {x y : Cochain c.pt L n}
    (h : ∀ j, (Cochain.ofHom (c.inj j)).comp x (zero_add n) = (Cochain.ofHom (c.inj j)).comp y (zero_add n)) : x = y := by
  ext p q hpq
  refine hom_ext_v c hc fun j => ?_
  have := congrArg (fun z => Cochain.v z p q hpq) (h j)
  simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this

def cof (L : CochainComplex C ℤ) {n : ℤ} (b : ∀ j, Cochain (K j) L n) (p q : ℤ) (hpq : p + n = q) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) where
  pt := L.X q
  ι :=
    { app := fun k => (b k.as).v p q hpq
      naturality := by
        rintro ⟨i⟩ ⟨k⟩ ⟨⟨h⟩⟩
        cases h
        exact (Category.id_comp _).trans (Category.comp_id _).symm }

def glue (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {n : ℤ}
    (b : ∀ j, Cochain (K j) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hc p).desc (cof L b p q hpq)

theorem restr_glue {n : ℤ} (b : ∀ j, Cochain (K j) L n) (j : ι) :
    (Cochain.ofHom (c.inj j)).comp (glue c hc b) (zero_add n) = b j := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hc p).fac (cof L b p q hpq) ⟨j⟩

include hc in
theorem bij (n : ℤ) : Function.Bijective fun (x : CohomologyClass c.pt L n) (j : ι) =>
    cpre (Cocycle.ofHom (c.inj j)) L n n (zero_add n) x := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    have hj : ∀ j, ∃ β : Cochain (K j) L (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj j)).comp (x - y : Cocycle c.pt L n).1 (zero_add n) := by
      intro j
      have h := congrFun hxy j
      simp only [cpre_mk] at h
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)] at h
      obtain ⟨β, hβ⟩ := h
      refine ⟨β, ?_⟩
      rw [hβ]
      simp [zcomp, Cochain.comp_sub]
    choose β hβ using hj
    refine ⟨glue c hc β, cochain_ext c hc fun j => ?_⟩
    rw [← δ_ofHom_comp, restr_glue, hβ]
  · intro y
    choose z hz using fun j => (y j).mk_surjective
    have hδ : δ n (n + 1) (glue c hc fun j => (z j).1) = 0 := cochain_ext c hc fun j => by
      rw [← δ_ofHom_comp, restr_glue, Cocycle.δ_eq_zero]; simp
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hδ), funext fun j => ?_⟩
    simp only [cpre_mk]
    rw [← hz j]
    congr 1
    exact Cocycle.ext (restr_glue c hc (fun j => (z j).1) j)

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem HKCoprod_of : LateralTheory.E.CoprodPf.HKCoprod := by
  intro R _ ι K c hc F n
  have h1 : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits.{1} (Shv R)
  have h0 : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} (Shv R)
  have : HasColimitsOfShape (Discrete ι) (Shv R) := inferInstance
  exact bij c (fun p => isColimitOfPreserves (HomologicalComplex.eval _ _ p) hc) n

end LateralTheory.E.HKCoprodPf
