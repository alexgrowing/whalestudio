import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem exists_finite_point_mem_closed {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [LocallyOfFiniteType s]
    {Z : Set X} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L) (z : Sp L ⟶ X), j.Finite ∧ z ≫ s = spMap j ∧ ∀ q, z q ∈ Z := by
  obtain ⟨x, hxZ⟩ := hne
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  obtain ⟨y, hy⟩ : x ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hxU
  let R := Γ(X, U)
  let φ : CommRingCat.of K ⟶ R := Spec.preimage (hU'.fromSpec ≫ s)
  have hφ : Spec.map φ = hU'.fromSpec ≫ s := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]; exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have hφft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  let _ : Algebra K R := φ.hom.toAlgebra
  have : Algebra.FiniteType K R := hφft
  let p : PrimeSpectrum R := y
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let L := R ⧸ m
  let _ : Field L := Ideal.Quotient.field m
  have : Algebra.FiniteType K L :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  have hfin : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  let ψ : R →+* L := Ideal.Quotient.mk m
  refine ⟨L, inferInstance, algebraMap K L, spMap ψ ≫ hU'.fromSpec, RingHom.finite_algebraMap.2 hfin, ?_, fun q => ?_⟩
  · show spMap ψ ≫ hU'.fromSpec ≫ s = spMap (algebraMap K L)
    rw [← hφ, ← Spec.map_comp]
    rfl
  · let q' : PrimeSpectrum L := q
    have h1 : p ⤳ PrimeSpectrum.comap ψ q' := by
      rw [← PrimeSpectrum.le_iff_specializes]
      intro a ha
      show ψ a ∈ q'.asIdeal
      rw [show ψ a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)]
      exact zero_mem _
    have h2 : hU'.fromSpec y ⤳ hU'.fromSpec (spMap ψ q) := Specializes.map h1 hU'.fromSpec.continuous
    rw [hy] at h2
    exact h2.mem_closed hZ hxZ

theorem exists_alg_intFr_onComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), PointsOfFlagModel.BaseAt la β → PushInvertible Y.t.G Y.t.PP.L → ∀ Z : Comp Xo c, ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io), OnComp Z y ∧ y.IsAlg := by
  intro E _ _ _ H Dw l Xo c la O _ β Y hB hPI Z
  classical
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ _) inferInstance
  obtain ⟨L, _, j, z, hj, hz, hzZ⟩ := exists_finite_point_mem_closed (strK (Xo := Xo) (c := c))
    (isClosed_of_mem_irreducibleComponents _ Z.2) Z.2.1.nonempty
  have nL : NumberField L := by
    let _ : Algebra c.F L := j.toAlgebra
    have : Module.Finite c.F L := hj
    exact NumberField.of_module_finite c.F L
  obtain ⟨T, k, e, ho, hfin⟩ := locFld c.F L j la
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T (k.comp j) e ho
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp j).toAlgebra
  have hs : (spMap k ≫ z) ≫ Limits.pullback.snd _ _ = spMap (k.comp j) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ z) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T (k.comp j) Y hPI b hb y₀
  refine ⟨T, k.comp j, e, ho, y, fun q => ?_, hfin⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : ptF y = spMap k ≫ z := by
    apply Limits.pullback.hom_ext
    · exact (CompSplitPfB.cspB_lift_fst _ _).trans (h1.trans h0)
    · exact (CompSplitPfB.cspB_lift_snd _ _).trans hs.symm
  rw [h2]
  exact hzZ (spMap k q)

end GlobalTheory.FactorDepth
