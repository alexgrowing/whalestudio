import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVarStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncChartsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

noncomputable section

namespace PositivityTheory.Xgn.QuotientUniformizationCharts

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Alg

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem exists_arith [CharZero Ω] (hK : Nonempty K) (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ e : ℕ, IsArithVar (mCoordIdeal y) (e + 1) := by
  classical
  obtain ⟨s, hs⟩ := (AlgebraicIndependent.matroid ℚ Ω).exists_isBasis (GroundTheory.Heights₂.Heights.coneRatios y c)
    (Set.subset_univ _)
  obtain ⟨hi, hsub, halg⟩ := AlgebraicIndependent.matroid_isBasis_iff.1 hs
  have hfin : s.Finite := (Set.finite_range _).subset hsub
  haveI : Fintype s := hfin.fintype
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hr : Set.range (fun i => (e i : Ω)) = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  refine ⟨Fintype.card s, GroundTheory.Heights₂.Heights.CoordConeArithVar.proof GroundTheory.Heights₂.Heights.IntDomainDim.full
    K J Ω y c _ (fun i => (e i : Ω)) hK hc ?_ (fun i => IntermediateField.subset_adjoin _ _ (hsub (e i).2)) ?_⟩
  · exact AlgebraicIndependent.comp hi e e.injective
  · intro r hr'
    rw [hr]
    exact IntermediateField.isAlgebraic_adjoin_iff.2 (halg r hr')

theorem evC_aeval (w : (Σ k, J k) → ℂ) (f : MRing J) : evC w f = aeval w f := evC_eq_aeval w f

theorem mem_ptsOver_iff (P : Ideal (MRing J)) (z : (Σ k, J k) → ℂ) : z ∈ Small.ptsOver ℂ P ↔ z ∈ mcPts P := by
  refine and_congr Iff.rfl (forall₂_congr fun f _ => ?_)
  rw [← evC_aeval]
  rfl

theorem torus_mem {P : Ideal (MRing J)} (hP : IsMultiHomogIdeal P) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P)
    (b : K → ℂ) (hb : ∀ k, b k ≠ 0) : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b z ∈ mcPts P := by
  rw [← mem_ptsOver_iff] at hz ⊢
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hb k) hi⟩
  · obtain ⟨S, hS, rfl⟩ := hP
    have hle : Ideal.span S ≤ RingHom.ker
        (aeval (GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b z) : MRing J →ₐ[ℤ] ℂ).toRingHom := by
      rw [Ideal.span_le]
      intro g hg
      obtain ⟨d, hd⟩ := hS g hg
      show aeval (fun p : Σ k, J k => b p.1 * z p) g = 0
      rw [GlobalTheory.CompanionTheory.Ar.LocVal.aeval_scale hd, hz.2 g (Ideal.subset_span hg), mul_zero]
    exact fun f hf => hle hf

theorem exists_charts (hR : Geo.ResK.ResKStatement) [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : MRing J) (b : K → ℕ) (hβ : IsMultiHomog β b) (hβ0 : β ∉ mCoordIdeal y) :
    ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧
      (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧
      (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → evC (w i t) β ≠ 0) ∧
      ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧
        x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  classical
  rcases isEmpty_or_nonempty K with hK | hK
  · haveI : IsEmpty (Σ k, J k) := ⟨fun p => hK.false p.1⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, β = C m := ⟨_, eq_C_of_isEmpty β⟩
    refine ⟨0, 1, fun _ _ => 0, fun _ => 0, fun _ => le_rfl, fun _ => analyticOnNhd_const, fun _ t _ => ?_,
      fun _ t _ _ => ?_, fun x _ => ⟨0, 0, fun _ => 1, by rw [norm_zero]; norm_num, fun _ => one_ne_zero, Subsingleton.elim _ _⟩⟩
    · refine ⟨fun k => (hK.false k).elim, fun f hf => ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m : ℤ, f = C m := ⟨_, eq_C_of_isEmpty f⟩
      have h : m' ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := hf
      rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.horizontal y] at h
      obtain rfl : m' = 0 := h
      simp
    · have hm : m ≠ 0 := by
        rintro rfl
        exact hβ0 (by simp)
      simpa [evC] using hm
  obtain ⟨e, he⟩ := exists_arith hK y c hc
  obtain ⟨M, y', I, hy', hfn, hI, -, hsnc, hbd⟩ := GlobalTheory.T.adjoin_coords_arith_var hR K J Ω y e β b he hβ hβ0
  have eL : joinVec y y' ∘ joinInl J (fun _ : Unit => Fin M) = y := rfl
  have hA : IsArithVar (mCoordIdeal (joinVec y y')) (e + 1) := by
    have hblock : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ Unit) (joinInl J fun _ : Unit => Fin M) := by
      refine ⟨Sum.inl_injective, GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.joinInl_injective, fun _ => rfl, ?_⟩
      rintro ⟨_, q⟩ ⟨k, rfl⟩
      exact ⟨⟨k, q⟩, rfl⟩
    have hnz : ∀ k, ∃ q, joinVec y y' ⟨k, q⟩ ≠ 0 := by
      intro k
      cases k with
      | inl k => exact ⟨c k, hc k⟩
      | inr k => exact hy'
    refine GlobalTheory.T.isArithVar_of_block_algebraic _ _ _ _ Sum.inl (joinInl J fun _ : Unit => Fin M) Ω (joinVec y y') _ hblock hnz
      (by rw [eL]; exact he) fun t ht => ?_
    rw [eL]
    exact isAlgebraic_algebraMap (⟨t, hfn ▸ ht⟩ : ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField y)
  obtain ⟨nc, χ, hχ⟩ := GlobalTheory.T.exists_torus_stable_snc_charts _ _ Ω (joinVec y y') e I hsnc hA fun z hz b' hb' =>
    ⟨torus_mem hA.2.1.2.1 hz.1 b' hb', torus_mem hI hz.2 b' hb'⟩
  refine ⟨e, nc, fun i t p => (χ i).γ t (joinInl J (fun _ : Unit => Fin M) p), fun i => (χ i).a, fun i => (χ i).a_le,
    fun i => ?_, fun i t ht => ?_, fun i t ht hne h0 => ?_, fun x hx => ?_⟩
  · exact AnalyticOnNhd.pi fun p => ((analyticOnNhd_pi_iff.1 (χ i).analytic) _)
  · have hz := (mem_ptsOver_iff _ _).2 ((χ i).mem t ht)
    refine (mem_ptsOver_iff _ _).1 ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
    have h1 := hz.2 _ (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.rename_mem (κ := Sum.inl) (v := joinInl J fun _ : Unit => Fin M)
      (fun _ => rfl) (joinVec y y') (f := f) hf)
    rw [aeval_rename] at h1
    exact h1
  · have h1 : (χ i).γ t ∈ mcPts I := by
      refine hbd _ ((χ i).mem t ht) ?_
      rw [evC_aeval, aeval_rename]
      rw [evC_aeval] at h0
      exact h0
    obtain ⟨j, hj, hj0⟩ := ((χ i).boundary t ht).1 ⟨(χ i).mem t ht, h1⟩
    exact hne j hj hj0
  · obtain ⟨z, hz, hzx⟩ := GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.exists_join_lift y y' (fun _ => hy') x ((mem_ptsOver_iff _ _).2 hx)
    obtain ⟨i, t, ht, b', hb', hzb⟩ := hχ z ((mem_ptsOver_iff _ _).1 hz)
    refine ⟨i, t, fun k => b' (Sum.inl k), ht, fun k => hb' _, ?_⟩
    rw [← hzx, hzb]
    rfl

theorem exists_form_off {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (c : ∀ k, J k) (f : MRing J) (b : K → ℕ), (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ IsMultiHomog f b ∧ f ∉ mCoordIdeal y ∧
      ∀ w : (Σ k, J k) → ℂ, evC w f ≠ 0 →
      ∀ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w → centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c ⟨ev ξ U hη s, (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩⟩
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨c, G₀ * cMon c 1, m + 1, hc, homog_mul hG₀ (homog_cMon c 1),
    fun hmem => hf0 (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.aeval_eq_zero_of_mem hmem), fun w hne z hz => ?_⟩
  rw [evC_aeval, map_mul, aeval_cMon] at hne
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne) k (Finset.mem_univ k)
    simpa using this
  let q : Cpt ξ := ⟨centre z, hall _⟩
  have hst : ∀ p : Σ k, J k, ∃ t : X.presheaf.stalk q.1, genMap ξ q t = y p / y ⟨p.1, c p.1⟩ ∧
      (Scheme.stalkClosedPointTo z).hom t = w p / w ⟨p.1, c p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, ⟨_, t, ht, htr⟩, hr⟩ := (hz.2 k (c k) (IsUnit.mk0 _ (hwc k))).2 i
    refine ⟨t, ht, ?_⟩
    rw [eq_div_iff (hwc k), hr]
    exact congrArg (· * _) htr
  choose t ht htw using hst
  have hq : q.1 ∈ U := by
    refine (hUm _).2 ⟨q.2, hcx, fun c' => ?_⟩
    simp only [← Finset.prod_div_distrib]
    exact Subring.prod_mem _ fun k _ => ⟨t ⟨k, c' k⟩, ht _⟩
  have hgerm : X.presheaf.germ U q.1 hq s = aeval t g₀ := by
    apply hT.gen.inj q
    rw [genMap_germ hη q hq s, ← hy₀]
    have h' := comp_aeval_apply (R := ℤ) t (genMap ξ q).toIntAlgHom g₀
    refine Eq.trans ?_ h'.symm
    congr 2
    funext p
    exact (ht p).symm
  have hval : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U q.1 hq s) =
      aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) g₀ := by
    rw [hgerm]
    have h' := comp_aeval_apply (R := ℤ) t (Scheme.stalkClosedPointTo z).hom.toIntAlgHom g₀
    refine h'.trans ?_
    congr 2
    funext p
    exact htw p
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U q.1 hq s) ≠ 0 := by
    rw [hval]
    intro h0
    apply left_ne_zero_of_mul hne
    rw [← eG ℂ w hwc, h0, zero_mul]
  exact hsV ((Scheme.mem_basicOpen X s _ hq).2
    (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0)))

end Alg

theorem exists_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) :
    ∃ V : 𝔐.X.Opens, genPt 𝔐.ξ ∈ V ∧ ∀ z : Sp ℂ ⟶ 𝔐.X, centre z ∈ V → 𝔐.Interior z := by
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 (IsFractionRing.injective (𝓞 c.F) c.F)
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  have hind : Topology.IsInducing (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing
  have hopen : IsOpen (Set.range Y.jQ) := by
    haveI := Y.jQ_open
    exact Y.jQ.isOpenEmbedding.isOpen_range
  obtain ⟨C, hC, hCe⟩ := hind.isClosed_iff.1 hopen.isClosed_compl
  refine ⟨⟨(𝔐.f ⁻¹' C)ᶜ, (hC.preimage 𝔐.f.continuous).isOpen_compl⟩, ?_, fun z hzV => ?_⟩
  · change 𝔐.f (genPt 𝔐.ξ) ∉ C
    have h1 : 𝔐.f (genPt 𝔐.ξ) = pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (Y.jQ (genPt x)) := by
      have h := congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of Ω))) hx
      exact h
    rw [h1]
    intro hin
    have : Y.jQ (genPt x) ∈ (Set.range Y.jQ)ᶜ := by
      rw [← hCe]
      exact hin
    exact this ⟨_, rfl⟩
  refine (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)).1 ?_
  obtain ⟨u, hu⟩ := exists_lift_genFibre Y.s (z ≫ 𝔐.f)
  let u₀ := u (IsLocalRing.closedPoint (CommRingCat.of ℂ))
  have hfu : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) u₀ = 𝔐.f (centre z) := by
    have := congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of ℂ))) hu
    exact this
  have hr : u₀ ∈ Set.range Y.jQ := by
    by_contra hn
    have : u₀ ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' C := by
      rw [hCe]
      exact hn
    apply hzV
    rw [Set.mem_preimage, hfu] at this
    exact this
  rw [← Y.ab_gen] at hr
  rw [← hfu]
  exact hr

end PositivityTheory.Xgn.QuotientUniformizationCharts

end

open PositivityTheory.Xgn.QuotientUniformizationCharts in
theorem PositivityTheory.Xgn.quotient_uniformization_charts : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  intro hR E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨V, hV, hint⟩ := exists_open 𝔐
  obtain ⟨c₀, β, b, hc, hβ, hβ0, hoff⟩ := exists_form_off 𝔐.ξ y 𝔐.all 𝔐.tie V hV
  obtain ⟨n, nc, w, a, h1, h2, h3, h4, h5⟩ := exists_charts hR y c₀ hc β b hβ hβ0
  exact ⟨n, nc, w, a, h1, h2, h3, fun i t ht hne z hz => hint z (hoff _ (h4 i t ht hne) z hz), h5⟩
