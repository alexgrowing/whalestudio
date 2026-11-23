import Development.EtaleCohomology.WeilConjectures.ContinCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.StabPf

section Proj
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) {X : Scheme.{0}} (p : X ⟶ Sp K)

def proj : geom Ω p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

theorem galMap_proj (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ L.fixingSubgroup) : galMap Ω p σ ≫ proj L p = proj L p := by
  apply pullback.hom_ext
  · simp only [proj, Category.assoc, pullback.lift_fst, galMap_fst]
  · simp only [proj, Category.assoc, pullback.lift_snd]
    rw [galMap_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact (mem_fixingSubgroup_iff _).1 hσ x x.2

end Proj

def Desc : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (k : ℕ)
    (y : HtL l k (sch.obj (geom (AlgebraicClosure K) p)) n 0),
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (z : HtL l k (sch.obj (geom L p)) n 0), pull _ (sch.map (proj L p)) _ n z = y

end LateralTheory.EWeil.StabPf
