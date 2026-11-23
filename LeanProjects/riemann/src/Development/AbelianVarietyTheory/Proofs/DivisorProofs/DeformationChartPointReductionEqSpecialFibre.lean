import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem mk_algebraMap_eq_mk_baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B]
    (d : DualNumber K) :
    Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps}) (algebraMap (DualNumber K) B d) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})
        (baseMap K B (TrivSqZeroExt.fst d)) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨algebraMap (DualNumber K) B (TrivSqZeroExt.inl d.snd), ?_⟩
  rw [← map_mul, RingHom.comp_apply, ← map_sub]
  congr 1
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem chartPt_red : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  intro K _ A _ A' _ i hi X Z h y1 m m' hm' him Ω δ n u θ Wo g B _ _ x l hx hxΩ hl
  set I : Ideal B := Ideal.span {algebraMap (DualNumber K) B DualNumber.eps} with hI
  set q : B →+* B ⧸ I := Ideal.Quotient.mk I with hq
  obtain ⟨h1, h2, h3⟩ := hl
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := fun p hp => hxΩ hp
  have hA : (spMap q ≫ l) ≫ A'.hom = (spMap q ≫ x ≫ i) ≫ A'.hom := by
    have e : q.comp (algebraMap (DualNumber K) B) =
        ((q.comp (baseMap K B)).comp (TrivSqZeroExt.fstHom K K K).toRingHom) :=
      RingHom.ext fun d => mk_algebraMap_eq_mk_baseMap K B d
    rw [Category.assoc, h1, Category.assoc, Category.assoc, hi.1.w, ← Category.assoc x, hx, GlobalTheory.DeRham.epsRed]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
  have hZ : (spMap q ≫ l) ≫ m' = (spMap q ≫ x ≫ i) ≫ m' := by
    have ha : ⊤ ≤ (spMap q ≫ l ≫ m') ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ h2
    have hb : ⊤ ≤ (spMap q ≫ x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ hxm
    have e : ev (spMap q ≫ l ≫ m') Ω.1 ha = ev (spMap q ≫ x ≫ m) Ω.1 hb := by
      rw [GlobalTheory.FlagMod.ev_spMap q _ _ h2, GlobalTheory.FlagMod.ev_spMap q _ _ hxm]
      ext f
      simp only [RingHom.comp_apply]
      rw [← valR_eq_ev _ _ h2, ← valR_eq_ev _ _ hxm, h3 f, chartVal, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl : _ ∈ I), zero_mul, add_zero]
    rw [Category.assoc, Category.assoc, Category.assoc, him,
      ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ l ≫ m') Ω.2 ha, ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ x ≫ m) Ω.2 hb, e]
  exact hm'.hom_ext hZ hA

end GlobalTheory.CechKS
