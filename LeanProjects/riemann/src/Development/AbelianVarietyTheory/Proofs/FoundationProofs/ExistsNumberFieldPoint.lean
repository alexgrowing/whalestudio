import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecCut

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt

theorem exists_finite_point {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [LocallyOfFiniteType s]
    {Z : Set X} (hZ : IsOpen Z) (hne : Z.Nonempty) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L) (g : Sp L ⟶ X), j.Finite ∧ g ≫ s = spMap j ∧ ∀ p, g p ∈ Z := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hU, hxU, hUZ⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⟨Z, hZ⟩ : X.Opens) from hx)
  have hU' : IsAffineOpen U := hU
  obtain ⟨y, -⟩ : x ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hxU
  let R := Γ(X, U)
  let φ : CommRingCat.of K ⟶ R := Spec.preimage (hU'.fromSpec ≫ s)
  have hφ : Spec.map φ = hU'.fromSpec ≫ s := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]; exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have hφft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  let : Algebra K R := φ.hom.toAlgebra
  have : Algebra.FiniteType K R := hφft
  let p : PrimeSpectrum R := y
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let L := R ⧸ m
  let fL : Field L := Ideal.Quotient.field m
  have : Algebra.FiniteType K L :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  have hf : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  refine ⟨L, fL, algebraMap K L, spMap (Ideal.Quotient.mk m) ≫ hU'.fromSpec, RingHom.finite_algebraMap.2 hf, ?_,
    fun q => hUZ ?_⟩
  · rw [Category.assoc, ← hφ]
    exact (Spec.map_comp _ _).symm
  · show _ ∈ (U : Set X)
    rw [← hU'.range_fromSpec, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev prX (Xo : Moduli Dw l) (c : Coeff l) : Xo.XF c ⟶ Xo.X :=
  pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

theorem exists_numberField_point (Z : Comp Xo c) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (j : c.F →+* L) (g : Sp L ⟶ Xo.XF c),
      g ≫ strK = spMap j ∧ ∀ p, g p ∈ (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) := inferInstance
  obtain ⟨L, _, j, g, hj, hg, hZ⟩ := exists_finite_point (strK (Xo := Xo) (c := c))
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z).isOpen
    (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  let _ : Algebra c.F L := j.toAlgebra
  have : Module.Finite c.F L := hj
  exact ⟨L, inferInstance, NumberField.of_module_finite c.F L, j, g, hg, hZ⟩

theorem prX_over {S : Type} [CommRing S] [Algebra c.F S] {g : Sp S ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap (algebraMap c.F S)) : (g ≫ prX Xo c) ≫ Xo.s = sOf c S := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hg, sOf, ← Spec.map_comp]
  rfl

theorem ptF_eq {S : Type} [CommRing S] [Algebra c.F S] {g : Sp S ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap (algebraMap c.F S)) {y : FrPt Xo c S} (hy : y.x = g ≫ prX Xo c) : ptF y = g := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, hy]
  · rw [ptF, pullback.lift_snd]
    exact hg.symm

theorem point_ext {Z : Comp Xo c} {L S : Type} [CommRing L] [CommRing S] {j : c.F →+* L} {g : Sp L ⟶ Xo.XF c}
    (hg : g ≫ strK = spMap j) (hZ : ∀ p, g p ∈ (Z : Set (Xo.XF c))) (k : L →+* S) :
    (spMap k ≫ g) ≫ strK = spMap (k.comp j) ∧ ∀ p, (spMap k ≫ g) p ∈ (Z : Set (Xo.XF c)) := by
  refine ⟨?_, fun p => ?_⟩
  · rw [Category.assoc, hg, ← Spec.map_comp]
    rfl
  · rw [Scheme.Hom.comp_apply]
    exact hZ _

theorem framesOn_nonempty {r : ℕ} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (hU : IsUnf U) (Z : Comp Xo c) :
    (framesOn U Z).Nonempty := by
  obtain ⟨L, _, _, j, g, hg, hZ⟩ := exists_numberField_point Z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  letI : Algebra c.F L := j.toAlgebra
  let k : L →ₐ[c.F] CAt σ := IsAlgClosed.lift
  obtain ⟨h1, h2⟩ := point_ext hg hZ k.toRingHom
  have e : k.toRingHom.comp j = algebraMap c.F (CAt σ) := k.comp_algebraMap
  rw [e] at h1
  obtain ⟨y, hy⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (prX_over h1)
  obtain ⟨i, z, t, ht⟩ := hU.2.2.1 y
  refine ⟨⟨i, z.1⟩, z.2, fun p => ?_⟩
  have := ptF_eq h1 (ht.1.symm.trans hy)
  exact this ▸ h2 p

theorem valOn_nonempty (hE : IntFrExt Xo c) (Z : Comp Xo c) (w : HeightOneSpectrum (𝓞 c.F)) :
    (valOn Z w).Nonempty := by
  obtain ⟨L, _, _, j, g, hg, hZ⟩ := exists_numberField_point Z
  obtain ⟨T, k, e, ho, hfin⟩ := locFld c.F L j w
  obtain ⟨h1, h2⟩ := point_ext hg hZ k
  obtain ⟨T', i, r, hr, hi, hfin', y, hy⟩ := hE T (k.comp j) hfin ((spMap k ≫ g) ≫ prX Xo c)
    (letI := (k.comp j).toAlgebra; prX_over h1)
  obtain ⟨h3, h4⟩ := point_ext h1 h2 i
  letI := (i.comp (k.comp j)).toAlgebra
  have h5 : ptF y.1 = spMap i ≫ spMap k ≫ g := ptF_eq h3 (hy.trans (Category.assoc _ _ _).symm)
  exact ⟨_, PtV.mk w (ho.bc i hr hi) y ⟨hfin', fun p => h5 ▸ h4 p⟩ () trivial, rfl⟩

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem hasPts (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) : HasPts U Z := by
  obtain ⟨⟨-, -, -, -, hA, -⟩, h⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  refine ⟨fun σ => ⟨framesOn_nonempty (hU _ (goodEmb_goodOf c σ)) Z, fun z _ hz => ?_⟩,
    valOn_nonempty ((h hpq).2.2 hg).1 Z⟩
  haveI : _root_.IsReduced (CAt (goodOf c σ)) := inferInstanceAs (_root_.IsReduced ℂ)
  exact hA _ _

end GlobalTheory.FlatLine
