import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralSmoothChartFrameModuli
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

namespace GlobalTheory.FrameFreeRule

theorem fnAt_comp {X Y : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (g : X ⟶ Y) (f : Γ(Y, ⊤)) :
    fnAt (y ≫ g) f = fnAt y (g.appTop.hom f) := by
  simp only [fnAt, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem fnAt_spMap_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (y : Sp S ⟶ X)
    (f : Γ(X, ⊤)) : fnAt (spMap φ ≫ y) f = φ (fnAt y f) := by
  rw [fnAt_comp]
  exact congrArg (fun q => q.hom (y.appTop.hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem fnAt_id {S : Type} [CommRing S] (a : S) :
    fnAt (𝟙 (Sp S)) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) = a := by
  simp [fnAt]

theorem eq_zero_of_geometric {P : Scheme.{0}} [IsReduced P] (s : Γ(P, ⊤))
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), fnAt y s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  let K := AlgebraicClosure (P.residueField x)
  let y : Sp K ⟶ P := spMap (algebraMap (P.residueField x) K) ≫ P.fromSpecResidueField x
  have h0 : y.appTop.hom s = 0 := by
    have := h K y
    unfold fnAt at this
    exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective).1 this
  have h1 : y ⁻¹ᵁ P.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen_top]
    erw [h0]
    exact Scheme.basicOpen_zero _ _
  have h2 : (default : Sp K) ∈ y ⁻¹ᵁ P.basicOpen s := by
    change y default ∈ P.basicOpen s
    have : y default = x := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rwa [this]
  rw [h1] at h2
  exact h2

theorem hom_ext_of_geometric {P Y : Scheme.{0}} [IsReduced P] [IsAffine Y] (u v : P ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), y ≫ u = y ≫ v) : u = v := by
  refine ext_of_isAffine ?_
  ext r
  rw [← sub_eq_zero]
  refine eq_zero_of_geometric _ fun K _ _ y => ?_
  have := congrArg (fun q => fnAt q r) (h K y)
  simp only [fnAt_comp] at this
  unfold fnAt at this ⊢
  rw [map_sub, map_sub, sub_eq_zero]
  exact this

theorem exists_glue {X : Scheme.{0}} [IsReduced X] {ι : Type} (A : ι → Type) [∀ i, CommRing (A i)]
    (j : ∀ i, Sp (A i) ⟶ X) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (a : ∀ i, A i)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (i i' : ι) (χ : A i →+* K) (χ' : A i' →+* K),
      spMap χ ≫ j i = spMap χ' ≫ j i' → χ (a i) = χ' (a i')) :
    ∃ f : Γ(X, ⊤), ∀ i, fnAt (j i) f = a i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => Sp (A i)) j
    (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩)
  let ev : ∀ i, Polynomial ℤ →+* A i := fun i => Polynomial.eval₂RingHom (Int.castRingHom _) (a i)
  let g : ∀ i, Sp (A i) ⟶ Sp (Polynomial ℤ) := fun i => spMap (ev i)
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    have : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    refine hom_ext_of_geometric _ _ fun K _ _ y => ?_
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (y ≫ pullback.fst (j i) (j i'))
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective (y ≫ pullback.snd (j i) (j i'))
    have e := h K i i' χ.hom χ'.hom (by
      change Spec.map χ ≫ _ = Spec.map χ' ≫ _
      rw [hχ, hχ', Category.assoc, Category.assoc, pullback.condition])
    rw [← Category.assoc, ← Category.assoc, ← hχ, ← hχ']
    change spMap χ.hom ≫ spMap (ev i) = spMap χ'.hom ≫ spMap (ev i')
    rw [GlobalTheory.LocalFrame.spMap_spMap, GlobalTheory.LocalFrame.spMap_spMap]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simpa [ev] using e
  let G : X ⟶ Sp (Polynomial ℤ) := 𝒰.glueMorphisms g hg
  refine ⟨G.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X), fun i => ?_⟩
  have hi : j i ≫ G = g i := 𝒰.ι_glueMorphisms g hg i
  rw [← fnAt_comp, hi, ← Category.comp_id (g i), fnAt_spMap_comp, fnAt_id]
  simp [ev]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem evR_eq_of_chart (s : Rul Xo c) (hs : s ∈ sec Xo c 0 0)
    (hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K),
      y'.x = y.x → evR Xo c s y' = evR Xo c s y)
    {A : Type} [CommRing A] [IsDomain A] [Algebra c.F A] (u : FrPt Xo c A)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (χ : A →ₐ[c.F] K) (y : FrPt Xo c K)
    (hy : y.x = spMap χ.toRingHom ≫ u.x) : evR Xo c s y = χ (evR Xo c s u) := by
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c A K χ u
  rw [hfree K z y (hy.trans hz.1.symm)]
  have hT1 := GlobalTheory.TransferCompare.allTest_framed Xo c A u
  have hT2 := GlobalTheory.TransferCompare.allTest_framed Xo c K z
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c s hs.1 K _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ _ u z hT1.choose_spec.choose_spec.choose_spec hz)

theorem exists_fn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (s : Rul Xo c), s ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c s y' = evR Xo c s y) → ∃ f : Γ(Xo.XF c, ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K), evR Xo c s y = GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.fnAt (GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.basePt y) f := by
  intro E _ _ _ H D l Xo c s hs hfree
  choose A iA dA aA j u hj hp hsn _ hu using
    GlobalTheory.LocalFrame.exists_integral_chart_frame GlobalTheory.abelianSchemeLaws_all.2.secTwist E H D l Xo c
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsReduced (Xo.XF c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd _ _)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (p : Xo.XF c) (χ : A p →+* K),
      spMap χ ≫ j p = basePt y → evR Xo c s y = χ (evR Xo c s (u p)) := by
    intro K _ _ _ y p χ hχ
    have h1 : χ.comp (algebraMap c.F (A p)) = algebraMap c.F K := by
      have h2 : spMap (χ.comp (algebraMap c.F (A p))) = spMap (algebraMap c.F K) := by
        rw [← GlobalTheory.LocalFrame.spMap_spMap, ← hsn, ← Category.assoc, hχ]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    refine evR_eq_of_chart s hs hfree (u p) ⟨χ, fun r => RingHom.congr_fun h1 r⟩ y ?_
    change y.x = spMap χ ≫ _
    rw [hu, ← Category.assoc, hχ]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨f, hf⟩ := exists_glue A j (fun x => ⟨x, hp x⟩) (fun p => evR Xo c s (u p)) (by
    intro K _ _ p p' χ χ' hχ
    letI : Algebra c.F K := (χ.comp (algebraMap c.F (A p))).toAlgebra
    have hsn' : (spMap χ ≫ j p) ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
      rw [Category.assoc, hsn, GlobalTheory.LocalFrame.spMap_spMap]
    obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) ((spMap χ ≫ j p) ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsn', sOf, GlobalTheory.LocalFrame.spMap_spMap])
    have hb : spMap χ ≫ j p = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [← hy]; exact (pullback.lift_fst _ _ _).symm
      · rw [hsn']; exact (pullback.lift_snd _ _ _).symm
    exact (key K y p χ hb).symm.trans (key K y p' χ' (hχ.symm.trans hb)))
  refine ⟨f, fun K _ _ _ y => ?_⟩
  let p : Xo.XF c := basePt y default
  have hr : Set.range (basePt y) ⊆ Set.range (j p) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default]
    exact hp p
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (IsOpenImmersion.lift (j p) (basePt y) hr)
  have hb : spMap χ.hom ≫ j p = basePt y := by
    change Spec.map χ ≫ _ = _
    rw [hχ, IsOpenImmersion.lift_fac]
  rw [key K y p χ.hom hb, ← hb, fnAt_spMap_comp, hf]

end GlobalTheory.FrameFreeRule
