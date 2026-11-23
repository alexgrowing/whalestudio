import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

private theorem exists_toField {Ω : Type} [Field Ω] {Y : Scheme.{0}} [IsIntegral Y] (g : Sp Ω ⟶ Y) [IsDominant g] :
    ∃ φ : Y.functionField →+* Ω, (∀ U : Y.Opens, genericPoint Y ∈ U → ⊤ ≤ g ⁻¹ᵁ U) ∧
      (∀ U : Y.Opens, ⊤ ≤ g ⁻¹ᵁ U → genericPoint Y ∈ U) ∧
      ∀ (U : Y.Opens) (h : genericPoint Y ∈ U) (e : ⊤ ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)),
        ProjSpace.fnOn ⊤ (φ (Cartier.fnOf U h s)) = (g.appLE U ⊤ e).hom s := by
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  let η := genericPoint (Sp Ω)
  have hb : Function.Bijective (Cartier.fnOf (X := Sp Ω) ⊤ trivial) := by
    refine ⟨fnOf_injective _ _, fun a => ?_⟩
    obtain ⟨U, hU, s, hs⟩ := (Sp Ω).presheaf.germ_exist (x := η) a
    obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim η x) ▸ hU
    exact ⟨s, hs⟩
  let e₁ := RingEquiv.ofBijective _ hb
  let e₂ := RingEquiv.ofBijective _ (ProjSpace.fnOn_top_bijective (A := Ω))
  refine ⟨(e₂.symm.toRingHom.comp e₁.symm.toRingHom).comp (functionFieldMap g), fun U hU x _ => ?_,
    fun U hU => gen_mem (x := g η) (hU trivial), fun U h e s => ?_⟩
  · obtain ⟨_, hz, z, rfl⟩ := g.denseRange.inter_open_nonempty U U.isOpen ⟨_, hU⟩
    exact (Subsingleton.elim z x) ▸ hz
  · change e₂ (e₂.symm (e₁.symm (functionFieldMap g _))) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_eq]
    have hx : η ∈ g ⁻¹ᵁ U := e trivial
    change _ = Cartier.fnOf ⊤ trivial (resG _ e (g.app U s))
    refine Eq.trans ?_ (fnOf_resG e _ _).symm
    rw [← Cartier.algebraMap_germ (show g η ∈ U from hx), functionFieldMap_algebraMap,
      ← Cartier.algebraMap_germ hx]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply g U η hx s

private theorem dim_of_trdeg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp K) [LocallyOfFiniteType q] (e : Y.functionField ≃+* Ω)
    (he : ∀ a, e (toFunctionField q a) = algebraMap K Ω a) {D : ℕ} (hD : Algebra.trdeg K Ω = D) :
    topologicalKrullDim Y = D := by
  letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q)).hom.toAlgebra
  have hc : Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q) = CommRingCat.ofHom (toFunctionField q) :=
    Spec.map_injective ((Spec.map_preimage _).trans (genericFieldPoint_over q))
  let e' : Y.functionField ≃ₐ[K] Ω := { e with
    commutes' := fun a => (congrArg (fun f => e (CommRingCat.Hom.hom f a)) hc).trans (he a) }
  have ht : Algebra.trdeg K Y.functionField = D :=
    (le_antisymm (trdeg_le_of_injective e'.toAlgHom e'.injective)
      (trdeg_le_of_injective e'.symm.toAlgHom e'.symm.injective)).trans hD
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq q ht
  have h2 : (q ⁻¹' {genericPoint (Spec (CommRingCat.of K))} : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rwa [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph] at h1

private theorem eq_top_of_span {K V Ω ι : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (u : ι → V) (hu : Submodule.span K (Set.range u) = ⊤) (hg : GlobalTheory.DegVal.GenRatios ev)
    (L : Subfield Ω) (hc : ∀ a, algebraMap K Ω a ∈ L) (hr : ∀ k l, ev (u l) ≠ 0 → ev (u k) / ev (u l) ∈ L) :
    L = ⊤ := by
  obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
    by_contra! h0
    exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
  have key : ∀ v, ev v / ev (u l) ∈ L := fun v => by
    have hv : v ∈ Submodule.span K (Set.range u) := hu ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hr k l hl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_div]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def, mul_div_assoc]; exact mul_mem (hc a) hx
  have h : GlobalTheory.DegVal.ratioField ev ≤ L.toIntermediateField hc := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨v, w, rfl⟩
    rw [← div_div_div_cancel_right₀ hl]
    exact div_mem (key v) (key w)
  rw [hg.2] at h
  exact top_unique fun x _ => h (IntermediateField.mem_top (x := x))

open MvPolynomial in

private theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (D : ℕ) (hg : GlobalTheory.DegVal.GenRatios ev) (hD : 0 < imageDeg ev D) :
    Algebra.trdeg K Ω = D := by
  obtain ⟨N, b, F, hF⟩ := (imageDeg_pos_iff ev D).1 hD
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h0 => hg.1 (b.ext fun k => by simpa using congrFun h0 k)
  have hr : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ :=
    eq_top_of_span ev b b.span_eq hg _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun k l _ => Subfield.subset_closure (Or.inr ⟨k, l, rfl⟩)
  have := isPrime_coneIdeal (K := K) y
  have hk : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (D + 1 : ℕ) :=
    GlobalTheory.ChowExists.ringKrullDim_of_isChowFormInt (P := coneIdeal K y) (fun g hg n =>
      (mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous n g)).2
        ((mem_coneIdeal_iff y g).1 hg n)) hF
  obtain ⟨d, hd, hd'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : d = D + 1 := by exact_mod_cast hd.symm.trans hk
  let f := Ideal.kerLiftAlg (coneMap K y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hr A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain] at hd'
  exact Cardinal.add_one_inj.1 (by exact_mod_cast hd')

theorem _root_.GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D m : ℕ) (u : Fin (m + 1) → V),
    Submodule.span K (Set.range u) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
      IsProjOver q ∧ topologicalKrullDim Y = D ∧ (⨆ k, nonzeroLocus (t k) = ⊤) ∧ Function.Bijective ψ ∧
      (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i),
        ψ (ev (u k)) * fnOf _ h ((t l).f i) = ψ (ev (u l)) * fnOf _ h ((t k).f i) := by
  intro K V Ω _ _ _ _ _ ev D m u hu hg hD
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy : Ideal.span (Set.range y) = ⊤ := by
    obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
      by_contra! h0
      exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨l, rfl⟩) (Ne.isUnit hl)
  let p := ProjSpace.pt (algebraMap K Ω) y hy
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hqc : QuasiCompact p := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  obtain ⟨Y, hY, g, j, hdom, hj, hgj⟩ : ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (g : Sp Ω ⟶ Y) (j : Y ⟶ PSpace K m),
      IsDominant g ∧ IsClosedImmersion j ∧ g ≫ j = p :=
    ⟨p.image, isIntegral_image p, p.toImage, p.imageι, inferInstance, inferInstance, p.toImage_imageι⟩
  obtain ⟨φ, hm₁, hm₂, hφ⟩ := exists_toField g
  let B := (ProjSpace.O1 K m).pull j
  let t : Fin (m + 1) → B.Sec := fun k => Cartier.secPull (ProjSpace.coord K m k) j
  have hU : ∀ i : PUnit → Fin (m + 1), g ⁻¹ᵁ B.U i = ProjSpace.spOpen (y (i ⟨⟩)) := fun i => by
    rw [← ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy]
    refine (congrArg (g ⁻¹ᵁ ·) (pull_U (ProjSpace.O1 K m) j i)).trans ?_
    exact (Scheme.Hom.comp_preimage g j _).symm.trans (congrArg (· ⁻¹ᵁ _) hgj)
  have hmem : ∀ i : PUnit → Fin (m + 1), genericPoint Y ∈ B.U i ↔ y (i ⟨⟩) ≠ 0 := fun i => by
    constructor
    · intro h h0
      have := (hm₁ _ h).trans (hU i).le (show genericPoint (Sp Ω) ∈ (⊤ : (Sp Ω).Opens) from trivial)
      rw [ProjSpace.mem_spOpen, h0] at this
      exact this (zero_mem _)
    · intro h
      refine hm₂ _ (le_of_le_of_eq (fun x _ => ?_) (hU i).symm)
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (Ne.isUnit h))
  have hrat : ∀ (i : PUnit → Fin (m + 1)) (h : genericPoint Y ∈ B.U i) (l : Fin (m + 1)),
      φ (Cartier.fnOf _ h ((t l).f i)) * y (i ⟨⟩) = y l := fun i h l => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    have e₁ := (resG_self _ _).symm.trans (ProjSpace.resG_secPull_coord j l i le_rfl)
    have h' : ⊤ ≤ p ⁻¹ᵁ ProjSpace.chart K m (i ⟨⟩) :=
      (hm₁ _ h).trans ((hU i).trans (ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy _).symm).le
    rw [map_mul, hφ _ h (hm₁ _ h), ← ProjSpace.pullRatio_pt_mul (algebraMap K Ω) y hy (i ⟨⟩) l h']
    congr 1
    refine (congrArg _ e₁).trans ?_
    rw [ProjSpace.appLE_pullRatio]
    exact ProjSpace.pullRatio_of_eq hgj _ _
  have hconst : ∀ a, φ (toFunctionField (j ≫ PSpace.str K m) a) = algebraMap K Ω a := fun a => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    refine (hφ ⊤ trivial le_top (((Scheme.ΓSpecIso (.of K)).inv ≫ (j ≫ PSpace.str K m).appTop).hom a)).trans ?_
    have e : g ≫ j ≫ PSpace.str K m = spMap (algebraMap K Ω) := by
      rw [reassoc_of% hgj, ProjSpace.pt_str]
    have e' : (j ≫ PSpace.str K m).appTop ≫ g.appTop = (spMap (algebraMap K Ω)).appTop := by
      rw [← Scheme.Hom.comp_appTop, e]
    have e'' := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K Ω))
    rw [← e'] at e''
    exact congrArg (resG (Sp Ω) le_top) (congrArg (fun f => f.hom a) e'').symm
  have hsurj : Function.Surjective φ := by
    rw [← RingHom.fieldRange_eq_top_iff]
    refine eq_top_of_span ev u hu hg _ (fun a => ⟨_, hconst a⟩) fun k l hl => ?_
    exact ⟨_, eq_div_of_mul_eq hl (hrat (fun _ => l) ((hmem (fun _ => l)).2 hl) k)⟩
  let e : Y.functionField ≃+* Ω := RingEquiv.ofBijective φ ⟨RingHom.injective _, hsurj⟩
  have hft : LocallyOfFiniteType (j ≫ PSpace.str K m) := inferInstance
  refine ⟨Y, hY, j ≫ PSpace.str K m, B, LB.isLB_pull (ProjSpace.O1_isLB K m) _, t,
    e.symm.toRingHom, ⟨m, j, hj, rfl⟩, dim_of_trdeg _ e hconst (trdeg_eq ev D hg hD),
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord K m) _, e.symm.bijective, fun a => ?_,
    fun k l i h => ?_⟩
  · apply e.injective
    change e (e.symm _) = φ _
    rw [RingEquiv.apply_symm_apply, ← hconst]
    simp [toFunctionField, Cartier.fnOf, algX, Scheme.Hom.appLE]
  · apply e.injective
    have hi := (hmem i).1 h
    change e (e.symm (y k) * _) = e (e.symm (y l) * _)
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    change y k * φ _ = y l * φ _
    rw [eq_div_of_mul_eq hi (hrat i h l), eq_div_of_mul_eq hi (hrat i h k)]
    ring
