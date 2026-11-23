import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatValEqValAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEquationsHeightSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointsEquivFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSectionExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverHt

theorem card_lifts {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {G Y : Scheme.{0}} (π : G ⟶ Y) [IsFinite π] (w : G)
    (y : Sp K ⟶ Y) (hy : below y = π w) :
    Nat.card {z : Sp K ⟶ G // below z = w ∧ z ≫ π = y} = π.residueDegree w := by
  obtain ⟨ψ, rfl⟩ := ExtConj.factor y _ hy
  letI := (π.residueFieldMap w).hom.toAlgebra
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField (π w)) (G.residueField w) :=
    residueFieldMap_finite_of_locallyQuasiFinite π _
  haveI : CharZero (Y.residueField (π w)) := ψ.hom.charZero
  have hP (a : G.residueField w →ₐ[Y.residueField (π w)] K) :
      (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ G.fromSpecResidueField w) ≫ π =
        Spec.map ψ ≫ Y.fromSpecResidueField (π w) := by
    have h : π.residueFieldMap w ≫ CommRingCat.ofHom a.toRingHom = ψ :=
      CommRingCat.hom_ext a.comp_algebraMap
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    exact congrArg (fun t => Spec.map t ≫ Y.fromSpecResidueField (π w)) h
  let P : (G.residueField w →ₐ[Y.residueField (π w)] K) →
      {z : Sp K ⟶ G // below z = w ∧ z ≫ π = Spec.map ψ ≫ Y.fromSpecResidueField (π w)} :=
    fun a => ⟨Spec.map (CommRingCat.ofHom a.toRingHom) ≫ G.fromSpecResidueField w, ExtConj.below_comp w _, hP a⟩
  have hb : Function.Bijective P := by
    refine ⟨fun a b h => ?_, ?_⟩
    · have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ G.fromSpecResidueField w =
          Spec.map (CommRingCat.ofHom b.toRingHom) ≫ G.fromSpecResidueField w := congrArg (fun t => t.1) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · rintro ⟨z, hz, hz'⟩
      obtain ⟨χ, h⟩ := ExtConj.factor z w hz
      have h2 : Spec.map (π.residueFieldMap w ≫ χ) = Spec.map ψ := by
        rw [← cancel_mono (Y.fromSpecResidueField (π w)), ← hz', ← h, Spec.map_comp, Category.assoc,
          Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
      have h3 := Spec.map_injective h2
      exact ⟨⟨χ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext h⟩
  rw [← Nat.card_congr (Equiv.ofBijective P hb), Nat.card_eq_fintype_card, AlgHom.card]
  rfl

theorem finsum_lifts {k K : Type} [Field k] [Field K] [IsAlgClosed K] [CharZero K] (σ : k →+* K) {G Y : Scheme.{0}}
    (π : G ⟶ Y) [IsFinite π] (s : Y ⟶ Sp k) [LocallyOfFiniteType s] (w : G) (hw : IsClosed ({w} : Set G))
    (f : {y : Sp K ⟶ Y // y ≫ s = spMap σ} → ℝ) :
    ∑ᶠ z : {z : {z : Sp K ⟶ G // z ≫ π ≫ s = spMap σ} // below z.1 = w},
        f ⟨z.1.1 ≫ π, (Category.assoc _ _ _).trans z.1.2⟩ =
      π.residueDegree w * ∑ᶠ y : {y : {y : Sp K ⟶ Y // y ≫ s = spMap σ} // below y.1 = π w}, f y.1 := by
  classical
  letI := σ.toAlgebra
  have hx : IsClosed ({π w} : Set Y) := by
    have := π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  have h₁ : Finite {z : {z : Sp K ⟶ G // z ≫ π ≫ s = spMap σ} // below z.1 = w} := (ExtConj.closed_point_geometric_fibres_finite (π ≫ s) w hw).2
  have h₂ : Finite {y : {y : Sp K ⟶ Y // y ≫ s = spMap σ} // below y.1 = π w} := (ExtConj.closed_point_geometric_fibres_finite s _ hx).2
  have := Fintype.ofFinite {z : {z : Sp K ⟶ G // z ≫ π ≫ s = spMap σ} // below z.1 = w}
  have := Fintype.ofFinite {y : {y : Sp K ⟶ Y // y ≫ s = spMap σ} // below y.1 = π w}
  let g : {z : {z : Sp K ⟶ G // z ≫ π ≫ s = spMap σ} // below z.1 = w} →
      {y : {y : Sp K ⟶ Y // y ≫ s = spMap σ} // below y.1 = π w} := fun z =>
    ⟨⟨z.1.1 ≫ π, (Category.assoc _ _ _).trans z.1.2⟩, (Scheme.Hom.comp_apply _ _ _).trans (congrArg π z.2)⟩
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_fiberwise (s := Finset.univ) (g := g)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f y.1) fun z hz => by rw [← (Finset.mem_filter.1 hz).2],
    Finset.sum_const, nsmul_eq_mul, ← card_lifts π w y.1.1 y.2, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  congr 2
  exact Nat.card_congr
    ⟨fun z => ⟨z.1.1.1, z.1.2, congrArg (fun t => t.1.1) z.2⟩,
      fun z => ⟨⟨⟨z.1, by rw [← Category.assoc, z.2.2, y.1.2]⟩, z.2.1⟩, Subtype.ext (Subtype.ext z.2.2)⟩,
      fun _ => rfl, fun _ => rfl⟩

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem isPreimmersion_j : IsPreimmersion V.j :=
  have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h

theorem isAlgPt (w : V.G) (hw : IsClosed ({w} : Set V.G)) : IsAlgPt (V.j w) := by
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra
  obtain ⟨⟨⟨y, hy⟩, hyx⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) (V.π ≫ Y.str) w hw).1
  have h : (y ≫ V.j) ≫ V.p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, V.pb.w, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm
  have h2 := GeomPt.isAlgPt V.ar
    (⟨y ≫ V.j, h⟩ : GeomPt V.p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))
  subst hyx
  exact h2

theorem exists_equiv (w : V.G) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ V.X) [IsClosedImmersion i]
    (hZ : IsArithVar (i ≫ V.p) 0) (hx : i (genericPoint Z) = V.j w) (K : Type) [Field K] (σ : F →+* K) :
    ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ V.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃
      {y : {y : Sp K ⟶ V.G // y ≫ V.π ≫ Y.str = spMap σ} // below y.1 = w},
      ∀ y, (E y).1.1 ≫ V.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  have : CharZero K := charZero_of_injective_ringHom σ.injective
  have hgen (y : Sp K ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField K Z y).2.hom.charZero
  have hj := isPreimmersion_j V
  have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp]
    rfl
  have hw (y : {y : Sp K ⟶ Z // y ≫ (i ≫ V.p) = spMap (σ.comp (algebraMap (𝓞 F) F))}) :
      (y.1 ≫ i) ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [Category.assoc, y.2, hs]
  let f : {y : Sp K ⟶ Z // y ≫ (i ≫ V.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} →
      {y : {y : Sp K ⟶ V.G // y ≫ V.π ≫ Y.str = spMap σ} // below y.1 = w} := fun y =>
    ⟨⟨V.pb.lift (y.1 ≫ i) (spMap σ) (hw y), V.pb.lift_snd _ _ _⟩, by
      apply V.j.isEmbedding.injective
      rw [← hx, ← hgen y.1]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun t : Sp K ⟶ V.X => below t) (V.pb.lift_fst _ _ (hw y))).trans
          (Scheme.Hom.comp_apply _ _ _))⟩
  have hf (y) : (f y).1.1 ≫ V.j = y.1 ≫ i := V.pb.lift_fst _ _ _
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun y => ⟨hf y, hgen y.1⟩⟩
  · apply Subtype.ext
    rw [← cancel_mono i, ← hf, ← hf, h]
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨y', hy'⟩ := ClosurePts.lift_closed i (genericPoint Z) (y ≫ V.j)
      ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg V.j hyx).trans hx.symm))
    have h1 : y' ≫ (i ≫ V.p) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [← Category.assoc, hy', Category.assoc, V.pb.w, ← Category.assoc, hy, hs]
    refine ⟨⟨y', h1⟩, Subtype.ext (Subtype.ext (V.pb.hom_ext ((hf _).trans hy') ?_))⟩
    exact (f ⟨y', h1⟩).1.2.trans hy.symm

theorem card_emb (w : V.G) (hw : IsClosed ({w} : Set V.G)) :
    (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ) =
      Module.finrank ℚ F * (V.π.residueDegree w * Nat.card {y : AlgPt Y // below y.1 = V.π w}) := by
  have := isPreimmersion_j V
  have hx : IsClosed ({V.π w} : Set Y.X) := by
    have := V.π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  have h := finsum_lifts (algebraMap F (AlgebraicClosure F)) V.π Y.str w hw fun _ => 1
  have h₁ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure F) (V.π ≫ Y.str) w hw).2
  have h₂ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure F) Y.str _ hx).2
  have e (α : Type) [Finite α] : ∑ᶠ _ : α, (1 : ℝ) = Nat.card α := by
    have := Fintype.ofFinite α
    simp [finsum_eq_sum_of_fintype]
  rw [e, e] at h
  rw [ResidueCard.card_ringHom_eq, ResidueCard.card_parity_sign_length_of_eq (V.π ≫ Y.str) w hw, Nat.cast_mul, h]
  rfl

open Classical in

theorem height_eq {C : CxSt F} {A : Adl C Y} {L : HermLB V.p} {k : ℕ} (hL : V.Induces A L k) {w : V.G}
    (hw : IsClosed ({w} : Set V.G)) {h : V.X → ℝ} (H : L.IsArithHeight h) :
    h (V.j w) = (k : ℝ) * ((A.n : ℕ) : ℝ) * A.ht (V.π w) * Nat.card (V.X.residueField (V.j w) →+* ℂ) := by
  obtain ⟨r, hr, hun, hinf, hfin⟩ := hL
  have hx : IsClosed ({V.π w} : Set Y.X) := by
    have := V.π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (V.j w)
  have := V.ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := isAlgPt V w hw
  have hri : Set.range i = closure {V.j w} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ V.p) 0 := V.ar.of_isClosedImmersion i hcΓ hd
  have := isPreimmersion_j V
  let u : V.G.functionFieldˣ := Units.map V.φ.toMonoidHom (eqn A.D (V.π w))⁻¹ ^ k
  have hue (c) : ((u * r c : V.G.functionFieldˣ) : V.G.functionField) = V.φ (genAt A.D (V.π w)) ^ k * r c := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  have hu (c) (hc : w ∈ (L.B.pull V.j).U c) : UnitAt w ((u * r c : V.G.functionFieldˣ) : V.G.functionField) := by
    rw [hue]
    exact hun c w hc
  obtain ⟨s, hs, hval⟩ := RestrictRatSec.exists_restriction V.X V.G Z V.j i w hi L.B L.isLB r hr _ hu
  have hdeg := H.point Z i hcΓ hd s hs
  have hne := (ExtConj.main F).1

  obtain ⟨E, hE⟩ := exists_equiv V w Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have h₁ := FinSum.main F Z (i ≫ V.p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => k * A.lg v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ V.j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : V.j w ∈ L.B.U c := by
        have e₂ : V.j w = (yt ≫ i) (below (spMap (hne v).some.O.subtype)) := by
          rw [← (E y).2]
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp (AlgebraicClosure F) ⟶ V.X => below t) e₁.symm).trans (Scheme.Hom.comp_apply _ _ _))
        rw [e₂]
        exact hU trivial
      have hb : below ((E y).1.1 ≫ V.π) = V.π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.π (E y).2)
      refine (hfin v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩ (E y).1.1 (yt ≫ i)
        (fun _ => c) rfl e₁ hU).trans (congrArg (fun t => Real.log ((hne v).some.w t)) ?_)
      refine Eq.trans ?_ (hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc).symm
      exact congrArg (valAt (E y).1.1) ((congrArg (fun x => V.φ (genAt A.D x) ^ k * _) hb).trans (hue _).symm))
  have h₂ (v) : ∑ᶠ y, (k : ℝ) * A.lg v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩ =
      (k * V.π.residueDegree w : ℝ) *
        if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = V.π w), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond, mul_assoc]
    refine congrArg _ (Eq.trans ?_ (finsum_lifts (algebraMap F _) V.π Y.str w hw (A.lg v (hne v).some)))
    exact finsum_comp_equiv E (f := fun z => A.lg v (hne v).some ⟨z.1.1 ≫ V.π, (Category.assoc _ _ _).trans z.1.2⟩)
  replace h₁ := h₁.trans (congrArg (- ·) (finsum_congr h₂))

  have h₃ (σ : F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ V.p) (σ.comp (algebraMap (𝓞 F) F)), logNorm ((L.restr i).φ _) s y =
      (k * V.π.residueDegree w : ℝ) * ∑ᶠ (z : Pts Y σ) (_ : under z = V.π w),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (V.π w))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨E, hE⟩ := exists_equiv V w Z i hZ hi ℂ σ
    rw [← finsum_subtype_eq_finsum_cond, mul_assoc]
    refine Eq.trans ?_ (congrArg _ (finsum_lifts σ V.π Y.str w hw fun z : Pts Y σ =>
      Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (V.π w))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)))
    rw [mul_finsum]
    refine finsum_eq_of_bijective E E.bijective fun y => ?_
    have hp := CxPts.mem_ptsIn.1 (CxPts.mem_pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y)
    unfold logNorm
    generalize CxPts.pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = c at hp ⊢
    have hxc : V.j w ∈ L.B.U (c PUnit.unit) := by
      have := Set.mem_iInter.1 hp PUnit.unit
      rw [← hi, ← (hE y).2]
      exact this
    have hx' : under (E y).1 = w := (E y).2
    have hxc' : w ∈ (L.B.pull V.j).U c := Set.mem_iInter.2 fun _ => hxc
    set y₀ : Pts Y σ := ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩ with hy₀
    have hb : under y₀ = V.π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.π (E y).2)
    have e₁ := hinf σ (E y).1 y₀ (Points.PtsOver.map i rfl _ y) c rfl (hE y).1.symm (hx'.symm ▸ hxc')
    rw [hb, ← hue c] at e₁
    have h0 : ‖ratVal ((u * r c : V.G.functionFieldˣ) : V.G.functionField) (E y).1‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (by rw [hx']; exact hu c hxc'))
    have e₂ := congrArg Real.log e₁
    have h0' : C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (V.π w))) y₀ ^ k ≠ 0 :=
      right_ne_zero_of_mul (((mul_pow _ _ _).symm.trans e₁).trans_ne (mul_ne_zero (pow_ne_zero _ h0) (Real.exp_ne_zero _)))
    rw [mul_pow, Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero _)) h0',
      Real.log_mul (pow_ne_zero _ h0) (Real.exp_ne_zero _), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_exp, Real.log_exp, HtModel.ratVal_eq_valAt] at e₂
    have e₃ := hval ℂ _ _ (c PUnit.unit) (hE y).1 (E y).2 (hE y).2 hxc
    have e₄ := (L.φ _).pull_φ i rfl c y
    rw [HtModel.ratVal_eq_valAt]
    refine (congrArg₂ (fun a b => Real.log ‖a‖ - b / 2) e₃ e₄).trans ?_
    change Real.log ‖valAt (E y).1.1 ((u * r c : V.G.functionFieldˣ) : V.G.functionField)‖ - _ = _
    rw [Nat.cast_ofNat] at e₂
    linarith
  unfold HermLB.curveDeg at hdeg
  rw [h₁, ← finsum_eq_of_bijective _ (HtModel.bijective_comp F) fun σ => (h₃ σ).symm, hi,
    ← mul_finsum, ← mul_finsum, finsum_eq_sum_of_fintype (α := F →+* ℂ)] at hdeg
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = V.π w} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  rw [hdeg, card_emb V w hw, Adl.ht]
  field_simp
  ring

theorem main : GlobalTheory.Published.ArExists → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y)
    (A : Adl C Y) (L : HermLB V.p) (k : ℕ) (w : V.G), IsClosed ({w} : Set V.G) → V.Induces A L k →
    IsAlgPt (V.j w) ∧ IsPtHt L (V.j w) ((k : ℝ) * ((A.n : ℕ) : ℝ) * A.ht (V.π w)) := by
  intro HE F _ _ C Y V A L k w hw hL
  obtain ⟨h, H⟩ := (HE _ V.X V.p _ V.ar).1 L
  exact ⟨isAlgPt V w hw, h, H, height_eq V hL hw H⟩

end GlobalTheory.Mean4O.CoverHt
