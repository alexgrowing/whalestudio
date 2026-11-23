import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.ModelHt

open GlobalTheory.TrueGeo.FinSum in

theorem finite_support_finsum {F : Type} [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (q : Z ⟶ Sp (𝓞 F)) (hZ : IsArithVar q 0) (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v)
    (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ)
    (hl : ∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ,
      D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) :
    (Function.support fun v => ∑ᶠ y, l v y).Finite := by
  have := hZ.isNoetherian
  have := T.arithmetic_variety_dim_zero_finite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  have key (v : HeightOneSpectrum (𝓞 F)) : ∑ᶠ y, l v y =
      -∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) := by
    obtain ⟨t, ht⟩ := T.cartier_local_equation_common Z hZ.dim_eq.le D (q ⁻¹' {⟨v.asIdeal, v.isPrime⟩}) (q.finite_preimage_singleton _)
    have ht' (z : Z) (hz : (q z).asIdeal = v.asIdeal) : D.IsEqn z t := ht z (PrimeSpectrum.ext hz)
    have hv (y) : l v y = Real.log ((e v).w (valAt y.1 (t : Z.functionField))) := by
      obtain ⟨yt, h₁, h₂⟩ := exists_ext (e v) y.1 y.2
      obtain ⟨g, hg, h₃⟩ := hl v y yt h₁
      have hb : below y.1 = genericPoint Z := SmallSecHeight.eq_genericPoint hZ
        (Scheme.SpecToEquivOfField _ Z y.1).2.hom.charZero
      rw [h₃, ← div_mul_cancel₀ (g : Z.functionField) t.ne_zero,
        OfModel.valAt_mul _ (hb ▸ regAt_genericPoint _) (hb ▸ regAt_genericPoint _), map_mul,
        w_valAt _ _ yt h₁ ((ht' _ h₂).iff_unitAt.1 hg), one_mul]
    rw [finsum_congr hv]
    have h3 := T.product_formula_order F Z q hZ v (e v) t
    have h4 : ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
        ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (Scheme.ord (t : Z.functionField) z : ℝ) *
          Real.log (Nat.card (Z.residueField z)) :=
      finsum_congr fun z => finsum_congr fun hz => by rw [(ht' z hz).mult_eq]
    rw [h4, h3, neg_neg]
  refine (Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab) (D.finite_support_mult.image fun z => (q z).asIdeal)).subset ?_
  intro v hv
  by_contra hn
  apply hv
  show ∑ᶠ y, l v y = 0
  rw [key, neg_eq_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
  by_cases hz : (q z).asIdeal = v.asIdeal
  · have h0 : D.mult z = 0 := by
      by_contra h0
      exact hn ⟨z, h0, hz⟩
    simp [h0]
  · simp [hz]

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 F)}
  {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ X} {π : G ⟶ Y.X} [IsFinite π]

theorem isPreimmersion_j (pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))) : IsPreimmersion j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) pb.flip h

theorem isAlgPt (ar : IsArithVar p Y.dim) (pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))) (w : G) (hw : IsClosed ({w} : Set G)) : IsAlgPt (j w) := by
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra
  obtain ⟨⟨⟨y, hy⟩, hyx⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) (π ≫ Y.str) w hw).1
  have h : (y ≫ j) ≫ p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, pb.w, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm
  have h2 := GeomPt.isAlgPt ar
    (⟨y ≫ j, h⟩ : GeomPt p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))
  subst hyx
  exact h2

theorem exists_equiv (pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))) (w : G) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : IsArithVar (i ≫ p) 0) (hx : i (genericPoint Z) = j w) (K : Type) [Field K] (σ : F →+* K) :
    ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃
      {y : {y : Sp K ⟶ G // y ≫ π ≫ Y.str = spMap σ} // below y.1 = w},
      ∀ y, (E y).1.1 ≫ j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  have : CharZero K := charZero_of_injective_ringHom σ.injective
  have hgen (y : Sp K ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField K Z y).2.hom.charZero
  have hj := isPreimmersion_j pb
  have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp]
    rfl
  have hw (y : {y : Sp K ⟶ Z // y ≫ (i ≫ p) = spMap (σ.comp (algebraMap (𝓞 F) F))}) :
      (y.1 ≫ i) ≫ p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [Category.assoc, y.2, hs]
  let f : {y : Sp K ⟶ Z // y ≫ (i ≫ p) = spMap (σ.comp (algebraMap (𝓞 F) F))} →
      {y : {y : Sp K ⟶ G // y ≫ π ≫ Y.str = spMap σ} // below y.1 = w} := fun y =>
    ⟨⟨pb.lift (y.1 ≫ i) (spMap σ) (hw y), pb.lift_snd _ _ _⟩, by
      apply j.isEmbedding.injective
      rw [← hx, ← hgen y.1]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun t : Sp K ⟶ X => below t) (pb.lift_fst _ _ (hw y))).trans
          (Scheme.Hom.comp_apply _ _ _))⟩
  have hf (y) : (f y).1.1 ≫ j = y.1 ≫ i := pb.lift_fst _ _ _
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun y => ⟨hf y, hgen y.1⟩⟩
  · apply Subtype.ext
    rw [← cancel_mono i, ← hf, ← hf, h]
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨y', hy'⟩ := ClosurePts.lift_closed i (genericPoint Z) (y ≫ j)
      ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg j hyx).trans hx.symm))
    have h1 : y' ≫ (i ≫ p) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [← Category.assoc, hy', Category.assoc, pb.w, ← Category.assoc, hy, hs]
    refine ⟨⟨y', h1⟩, Subtype.ext (Subtype.ext (pb.hom_ext ((hf _).trans hy') ?_))⟩
    exact (f ⟨y', h1⟩).1.2.trans hy.symm

theorem card_emb (pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))) (w : G) (hw : IsClosed ({w} : Set G)) :
    (Nat.card (X.residueField (j w) →+* ℂ) : ℝ) =
      Module.finrank ℚ F * (π.residueDegree w * Nat.card {y : AlgPt Y // below y.1 = π w}) := by
  have := isPreimmersion_j pb
  have hx : IsClosed ({π w} : Set Y.X) := by
    have := π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  have h := CoverHt.finsum_lifts (algebraMap F (AlgebraicClosure F)) π Y.str w hw fun _ => 1
  have h₁ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure F) (π ≫ Y.str) w hw).2
  have h₂ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure F) Y.str _ hx).2
  have e (α : Type) [Finite α] : ∑ᶠ _ : α, (1 : ℝ) = Nat.card α := by
    have := Fintype.ofFinite α
    simp [finsum_eq_sum_of_fintype]
  rw [e, e] at h
  rw [ResidueCard.card_ringHom_eq, ResidueCard.card_parity_sign_length_of_eq (π ≫ Y.str) w hw, Nat.cast_mul, h]
  rfl

open Classical in

theorem height_eq (ar : IsArithVar p Y.dim) (pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))) (φ : Y.Fn →+* G.functionField) {C : CxSt F}
    {A : Adl C Y} {L : HermLB p} {k : ℕ} (r : (L.B.pull j).ι → G.functionFieldˣ) (hr : IsRatSec (L.B.pull j) r)
    (hun : ∀ i, ∀ x ∈ (L.B.pull j).U i, UnitAt x (φ (genAt A.D (π x)) ^ k * r i))
    (hinf : ∀ (σ : F →+* ℂ) (z : CxPts (π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull j).ι), y.1 = z.1 ≫ π → y'.1 = z.1 ≫ j → under z ∈ (L.B.pull j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (φ (genAt A.D (under y)) ^ k * (r i : G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y'))
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ G) (yt : Sp e.O ⟶ X)
      (i : (L.B.pull j).ι), z ≫ π = y.1 → spMap e.O.subtype ≫ yt = z ≫ j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (φ (genAt A.D (below y.1)) ^ k * (r i : G.functionField)))))
    {w : G} (hw : IsClosed ({w} : Set G)) {h : X → ℝ} (H : L.IsArithHeight h) :
    h (j w) = (k : ℝ) * ((A.n : ℕ) : ℝ) * A.ht (π w) * Nat.card (X.residueField (j w) →+* ℂ) ∧
      (k ≠ 0 → (Function.support fun v : HeightOneSpectrum (𝓞 F) => if hv : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = π w), A.lg v hv.some y else 0).Finite) := by
  have hx : IsClosed ({π w} : Set Y.X) := by
    have := π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (j w)
  have := ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := isAlgPt ar pb w hw
  have hri : Set.range i = closure {j w} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := ar.of_isClosedImmersion i hcΓ hd
  have := isPreimmersion_j pb
  let u : G.functionFieldˣ := Units.map φ.toMonoidHom (eqn A.D (π w))⁻¹ ^ k
  have hue (c) : ((u * r c : G.functionFieldˣ) : G.functionField) = φ (genAt A.D (π w)) ^ k * r c := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  have hu (c) (hc : w ∈ (L.B.pull j).U c) : UnitAt w ((u * r c : G.functionFieldˣ) : G.functionField) := by
    rw [hue]
    exact hun c w hc
  obtain ⟨s, hs, hval⟩ := RestrictRatSec.exists_restriction X G Z j i w hi L.B L.isLB r hr _ hu
  have hdeg := H.point Z i hcΓ hd s hs
  have hne := (ExtConj.main F).1

  obtain ⟨E, hE⟩ := exists_equiv pb w Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have hS := finite_support_finsum Z (i ≫ p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => k * A.lg v (hne v).some ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : j w ∈ L.B.U c := by
        have e₂ : j w = (yt ≫ i) (below (spMap (hne v).some.O.subtype)) := by
          rw [← (E y).2]
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp (AlgebraicClosure F) ⟶ X => below t) e₁.symm).trans (Scheme.Hom.comp_apply _ _ _))
        rw [e₂]
        exact hU trivial
      have hb : below ((E y).1.1 ≫ π) = π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg π (E y).2)
      refine (hfin v (hne v).some ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩ (E y).1.1 (yt ≫ i)
        (fun _ => c) rfl e₁ hU).trans (congrArg (fun t => Real.log ((hne v).some.w t)) ?_)
      refine Eq.trans ?_ (hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc).symm
      exact congrArg (valAt (E y).1.1) ((congrArg (fun x => φ (genAt A.D x) ^ k * _) hb).trans (hue _).symm))
  have h₁ := FinSum.main F Z (i ≫ p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => k * A.lg v (hne v).some ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : j w ∈ L.B.U c := by
        have e₂ : j w = (yt ≫ i) (below (spMap (hne v).some.O.subtype)) := by
          rw [← (E y).2]
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp (AlgebraicClosure F) ⟶ X => below t) e₁.symm).trans (Scheme.Hom.comp_apply _ _ _))
        rw [e₂]
        exact hU trivial
      have hb : below ((E y).1.1 ≫ π) = π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg π (E y).2)
      refine (hfin v (hne v).some ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩ (E y).1.1 (yt ≫ i)
        (fun _ => c) rfl e₁ hU).trans (congrArg (fun t => Real.log ((hne v).some.w t)) ?_)
      refine Eq.trans ?_ (hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc).symm
      exact congrArg (valAt (E y).1.1) ((congrArg (fun x => φ (genAt A.D x) ^ k * _) hb).trans (hue _).symm))
  have h₂ (v) : ∑ᶠ y, (k : ℝ) * A.lg v (hne v).some ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩ =
      (k * π.residueDegree w : ℝ) *
        if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = π w), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond, mul_assoc]
    refine congrArg _ (Eq.trans ?_ (CoverHt.finsum_lifts (algebraMap F _) π Y.str w hw (A.lg v (hne v).some)))
    exact finsum_comp_equiv E (f := fun z => A.lg v (hne v).some ⟨z.1.1 ≫ π, (Category.assoc _ _ _).trans z.1.2⟩)
  have hS' : k ≠ 0 → (Function.support fun v : HeightOneSpectrum (𝓞 F) => if hv : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = π w), A.lg v hv.some y else 0).Finite := fun hk => by
    have hd : π.residueDegree w ≠ 0 := by
      let := (π.residueFieldMap w).hom.toAlgebra
      have : Module.Finite (Y.X.residueField (π w)) (G.residueField w) :=
        residueFieldMap_finite_of_locallyQuasiFinite π _
      exact Module.finrank_pos.ne'
    refine hS.subset fun v hv => ?_
    rw [Function.mem_support] at hv ⊢
    intro h0
    have h3 := (h₂ v).symm.trans h0
    exact hv ((mul_eq_zero.1 h3).resolve_left (mul_ne_zero (Nat.cast_ne_zero.2 hk) (Nat.cast_ne_zero.2 hd)))
  replace h₁ := h₁.trans (congrArg (- ·) (finsum_congr h₂))

  have h₃ (σ : F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ p) (σ.comp (algebraMap (𝓞 F) F)), logNorm ((L.restr i).φ _) s y =
      (k * π.residueDegree w : ℝ) * ∑ᶠ (z : Pts Y σ) (_ : under z = π w),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (π w))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨E, hE⟩ := exists_equiv pb w Z i hZ hi ℂ σ
    rw [← finsum_subtype_eq_finsum_cond, mul_assoc]
    refine Eq.trans ?_ (congrArg _ (CoverHt.finsum_lifts σ π Y.str w hw fun z : Pts Y σ =>
      Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (π w))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)))
    rw [mul_finsum]
    refine finsum_eq_of_bijective E E.bijective fun y => ?_
    have hp := CxPts.mem_ptsIn.1 (CxPts.mem_pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y)
    unfold logNorm
    generalize CxPts.pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = c at hp ⊢
    have hxc : j w ∈ L.B.U (c PUnit.unit) := by
      have := Set.mem_iInter.1 hp PUnit.unit
      rw [← hi, ← (hE y).2]
      exact this
    have hx' : under (E y).1 = w := (E y).2
    have hxc' : w ∈ (L.B.pull j).U c := Set.mem_iInter.2 fun _ => hxc
    set y₀ : Pts Y σ := ⟨(E y).1.1 ≫ π, (Category.assoc _ _ _).trans (E y).1.2⟩ with hy₀
    have hb : under y₀ = π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg π (E y).2)
    have e₁ := hinf σ (E y).1 y₀ (Points.PtsOver.map i rfl _ y) c rfl (hE y).1.symm (hx'.symm ▸ hxc')
    rw [hb, ← hue c] at e₁
    have h0 : ‖ratVal ((u * r c : G.functionFieldˣ) : G.functionField) (E y).1‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (by rw [hx']; exact hu c hxc'))
    have e₂ := congrArg Real.log e₁
    have h0' : C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (π w))) y₀ ^ k ≠ 0 :=
      right_ne_zero_of_mul (((mul_pow _ _ _).symm.trans e₁).trans_ne (mul_ne_zero (pow_ne_zero _ h0) (Real.exp_ne_zero _)))
    rw [mul_pow, Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero _)) h0',
      Real.log_mul (pow_ne_zero _ h0) (Real.exp_ne_zero _), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_exp, Real.log_exp, HtModel.ratVal_eq_valAt] at e₂
    have e₃ := hval ℂ _ _ (c PUnit.unit) (hE y).1 (E y).2 (hE y).2 hxc
    have e₄ := (L.φ _).pull_φ i rfl c y
    rw [HtModel.ratVal_eq_valAt]
    refine (congrArg₂ (fun a b => Real.log ‖a‖ - b / 2) e₃ e₄).trans ?_
    change Real.log ‖valAt (E y).1.1 ((u * r c : G.functionFieldˣ) : G.functionField)‖ - _ = _
    rw [Nat.cast_ofNat] at e₂
    linarith
  unfold HermLB.curveDeg at hdeg
  rw [h₁, ← finsum_eq_of_bijective _ (HtModel.bijective_comp F) fun σ => (h₃ σ).symm, hi,
    ← mul_finsum, ← mul_finsum, finsum_eq_sum_of_fintype (α := F →+* ℂ)] at hdeg
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = π w} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  refine ⟨?_, hS'⟩
  rw [hdeg, card_emb pb w hw, Adl.ht]
  field_simp
  ring

omit [IsIntegral X] [IsIntegral G] [IsFinite π] in

theorem ht_twist_neg {C : CxSt F} (A : Adl C Y) {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hcf : (Function.support cf).Finite)
    {x : Y.X} (hx : IsClosed ({x} : Set Y.X))
    (hS : (Function.support fun v : HeightOneSpectrum (𝓞 F) => if hv : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (A.twist 0 (-cf)).lg v hv.some y else 0).Finite) :
    (A.twist 0 (-cf)).ht x = A.ht x - (∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ) := by
  classical
  obtain ⟨hN0, hNf⟩ := ExtConj.pts Y x hx
  have := Fintype.ofFinite {y : AlgPt Y // below y.1 = x}
  set N : ℝ := (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ) with hNdef
  have hsum (g : AlgPt Y → ℝ) (c : ℝ) : ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (g y + c) =
      (∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), g y) + N * c := by
    rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond (f := g), finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hNdef,
      Nat.card_eq_fintype_card]
  let SA : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if hv : Nonempty (Ext v) then
    ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v hv.some y else 0
  have hT (v : HeightOneSpectrum (𝓞 F)) : (if hv : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (A.twist 0 (-cf)).lg v hv.some y else 0) =
      SA v + N * ((A.n : ℕ) * cf v) := by
    have hne : Nonempty (Ext v) := inferInstance
    simp only [SA, dif_pos hne]
    simp only [Adl.twist, Pi.neg_apply, mul_neg, sub_neg_eq_add]
    exact hsum _ _
  have hc : (Function.support fun v => N * ((A.n : ℕ) * cf v)).Finite :=
    hcf.subset fun v hv h0 => hv (by simp [h0])
  have hSA : (Function.support SA).Finite := by
    refine (hS.union hc).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    apply hv
    have h3 := (hT v).symm.trans h.1
    rw [h.2, add_zero] at h3
    exact h3
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  have hsplit : ∑ᶠ v, (if hv : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (A.twist 0 (-cf)).lg v hv.some y else 0) =
      ∑ᶠ v, SA v + N * (A.n : ℕ) * ∑ᶠ v, cf v := by
    rw [finsum_congr hT, finsum_add_distrib hSA hc, mul_assoc, mul_finsum, mul_finsum]
  rw [Adl.ht, hsplit, Adl.ht]
  simp only [Adl.twist, Pi.add_apply, Pi.zero_apply, add_zero]
  field_simp
  ring

theorem main : GlobalTheory.Published.ArExists → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (P : TrueGeo.Model Y) (L : HermLB P.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced P L k cf →
    ∀ y : Y.X, IsClosed ({y} : Set Y.X) → IsPtHt L (P.j y) (((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * A.ht y -
      ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * (∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)) := by
  intro HE F _ _ C Y A P L k cf hI y hy
  have := P.ar.isIntegral
  obtain ⟨h, H⟩ := (HE _ P.X P.p _ P.ar).1 L
  have hcf := hI.1
  have hI' : (A.twist 0 (-cf)).Induced P L k 0 := by
    have h2 := hI.twist_fin (c := -cf) (by rwa [Function.support_neg])
    rwa [add_neg_cancel] at h2
  obtain ⟨-, r, hr, h₁, h₂⟩ := hI'
  have pb : IsPullback P.j (𝟙 Y.X ≫ Y.str) P.p (spMap (algebraMap (𝓞 F) F)) := by simpa using P.pb
  have hg (x : Y.X) : ((k : ℕ) • (A.twist 0 (-cf)).D).GeneratesAt x (genAt (A.twist 0 (-cf)).D x ^ (k : ℕ)) := by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn (A.twist 0 (-cf)).D x).nsmul k)
    rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
  obtain ⟨he, hS⟩ := height_eq P.ar pb (RingHom.id _) (A := A.twist 0 (-cf)) (k := (k : ℕ)) r hr.isRatSec
    (fun i x hx => (hr.isEqn i x hx).generatesAt_iff.1 (hg x))
    (fun σ z y y' i e₁ e₂ hi => by
      obtain rfl : y = z := Subtype.ext (e₁.trans (Category.comp_id _))
      have := h₁ σ y y' i _ e₂ hi (hg _).regularAt
      rw [C.pn_mPow Y σ (A.twist 0 (-cf)).D k _ _ y (generatesAt_genAt _ _)] at this
      rw [mul_pow, ← Real.exp_nat_mul]
      refine Eq.trans ?_ this
      congr 2
      ring)
    (fun v e y z yt i e₁ e₂ hi => by
      obtain rfl : z = y.1 := (Category.comp_id _).symm.trans e₁
      have := h₂ v e y yt i e₂ hi
      rw [Pi.zero_apply, mul_zero, sub_zero, Units.val_mul, Units.val_pow_eq_pow_val] at this
      exact this) hy H
  have e (x : Y.X) : (𝟙 Y.X : Y.X ⟶ Y.X) x = x := rfl
  simp only [e] at he hS
  have hn : (A.twist 0 (-cf)).n = A.n := rfl
  rw [hn, ht_twist_neg A hcf hy (hS (PNat.ne_zero k))] at he
  refine ⟨h, H, he.trans ?_⟩
  ring

end GlobalTheory.Mean4O.ModelHt
