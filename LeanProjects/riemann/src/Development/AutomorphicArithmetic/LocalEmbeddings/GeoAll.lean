import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimComponent
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberBaseChange
import Development.AutomorphicArithmetic.DivisorFrames.GenericFibreOpenProjective
import Development.AutomorphicArithmetic.DivisorFrames.PointsGenericFibreComponents
import Development.AutomorphicArithmetic.DivisorFrames.FunctionFieldEssFiniteTypeInt
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumbersAgreeModel
import Development.AutomorphicArithmetic.DivisorFrames.DegreeMatchingFamilies
import Development.AutomorphicArithmetic.DivisorFrames.NonemptyLevelStructure
import Development.AutomorphicArithmetic.DivisorFrames.LevelPointCount
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingFlag
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingMetric
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagMultiplicity
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagPrime

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Cartier

namespace GlobalTheory.ConsGeo.GenDeg

def num {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {d : ℕ} (c : Fin d → Pic X) : ℤ :=
  letI := algebraΓOfHom s
  multiDiff c (chiPic F (structureModule X)) 0

theorem num_eq {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {d : ℕ} {L : Fin d → LB X} (hL : ∀ i, (L i).IsLB) :
    num s (fun i => cls (L i) (hL i)) = (letI := algebraΓOfHom s; interNum F (structureModule X) L) :=
  letI := algebraΓOfHom s
  (interNum_eq_multiDiff F _ hL).symm

theorem num_comp {F K : Type} [Field F] [Field K] (b : F →+* K) (hb : 0 < embDeg b) {X : Scheme.{0}} (s : X ⟶ Sp K)
    (hs : IsProjOver s) {d : ℕ} (c : Fin d → Pic X) : num (s ≫ spMap b) c = (embDeg b : ℤ) * num s c := by
  choose L hL e using fun i => cls_surj (c i)
  obtain rfl : c = fun i => cls (L i) (hL i) := funext fun i => (e i).symm
  rw [num_eq _ hL, num_eq _ hL]
  exact (UpperTheory.intersection_number_base_change F K b X s hb hs).2 d L hL

theorem embDeg_conj {F K L M : Type} [Field F] [Field K] [Field L] [Field M] (e : F ≃+* K) (b : K →+* L) (ε : L ≃+* M) :
    embDeg (ε.toRingHom.comp (b.comp e.toRingHom)) = embDeg b := by
  letI := b.toAlgebra
  letI := (ε.toRingHom.comp (b.comp e.toRingHom)).toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv e.symm ε (RingHom.ext fun x => by
    simp [RingHom.algebraMap_toAlgebra])).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem letterOf_self (ℓ : Letter Dw) : letterOf Dw (.inl (ℓ.1, ℓ.2)) = some ℓ := dif_pos ℓ.2.2

variable {O : Type} [CommRing O] {β : O →+* i₀.c.F} {T : Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] [NumberField F]
  {e : F ≃+* i₀.c.F}

theorem divOf_single {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {β : O →+* c.F} {T : Model Xo c β} {e : F ≃+* c.F}
    (C : FlagCpt T e) (a : ℕ → Bool) (R : Option ℝ) (ℓ : Letter Dw) (m : ℤ) :
    divOf C (expo Dw (Finsupp.single (a, R, .inl (ℓ.1, ℓ.2)) m)) = m • C.gr ℓ.1 ℓ.2 := by
  classical
  have e (x : Letter Dw) : expo Dw (Finsupp.single (a, R, .inl (ℓ.1, ℓ.2)) m) x =
      if letterOf Dw (.inl (ℓ.1, ℓ.2)) = some x then m else 0 := by
    rw [expo, Finsupp.sum_single_index (by simp)]
  simp only [divOf, e]
  have h₁ := letterOf_self ℓ
  rw [Finset.sum_eq_single ℓ (fun b _ hb => by
      rw [if_neg fun h₂ => hb (Option.some.inj (h₂.symm.trans h₁)), zero_smul]) (by simp), if_pos h₁]

theorem sum_fibre (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hpq : 1 ≤ Dw.p + Dw.q) (z : admitted Y i₀)
    {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} [Fintype U.Comp] (Φ : FlagTor T e U) {d : ℕ}
    (hd : haveI := isDiscreteValuationRing_V z.Z.i.c hp hW; ∀ C, ((nmodel z.Z).comp C).relDim = d)
    (hd' : ∀ c, (Φ.C c).Y.dim = d) (x : Fin d → Letter Dw) (m : Fin d → ℤ) (hm : ∀ t, m t = 1 ∨ m t = -1) :
    haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    ∑ C, num ((nmodel z.Z).comp C).toBase.genFibreStr
        (fun t => pull (((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C)
          (m t • (z.line false _ (x t) (letterOf_self (x t))).L.cls)) =
      cov z * ∑ c, num (Φ.C c).Y.str fun t => toPic (m t • (Φ.C c).gr (x t).1 (x t).2) := by
  classical
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := z.Z.i.c.fin
  haveI := i₀.c.fin
  obtain ⟨L⟩ := UpperTheory.nonempty_level_structure z.Z T hpq
  choose hint hopen hrange hproj hdim ε hε using fun C : (nmodel z.Z).Comp =>
    UpperTheory.generic_fibre_open_projective (z.Z.i.c.V W) z.Z.i.c.F ((nmodel z.Z).comp C)
  let b : F →+* z.Z.i.c.F := (incl z.Z).comp e.toRingHom
  let ι (C : (nmodel z.Z).Comp) := ((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C
  let sK (C : (nmodel z.Z).Comp) := ((nmodel z.Z).comp C).toBase.genFibreStr ≫ spMap (ε C).toRingHom
  let sX (C : (nmodel z.Z).Comp) := ((nmodel z.Z).comp C).toBase.genFibreStr ≫ spMap ((ε C).toRingHom.comp b)
  have hsX (C) : sX C = sK C ≫ spMap (incl z.Z) ≫ spMap e.toRingHom := by
    simp only [sX, sK, b, Category.assoc, GlobalTheory.ModelRelProbe.spMap_comp]
  have hι (C) : ι C ≫ z.Z.s = sK C ≫ spMap (z.Z.i.c.V W).subtype := by
    simp only [ι, sK, Category.assoc]
    exact (congrArg (_ ≫ ·) (NModel.compι_str _ C)).trans (hε C).symm
  have hm0 : 0 < embDeg (incl z.Z) := by
    letI := (incl z.Z).toAlgebra
    haveI : Module.Finite i₀.c.F z.Z.i.c.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    exact Module.finrank_pos
  have hm' (C) : embDeg ((ε C).toRingHom.comp b) = embDeg (incl z.Z) := embDeg_conj e _ _
  have hpX (C) : IsProjOver (sX C) := (UpperTheory.intersection_number_base_change _ _ _ _ _ (hm' C ▸ hm0) (hproj C)).1
  haveI : ∀ C, LocallyOfFiniteType (sX C) := fun C => by
    have := projProper _ _ _ (hpX C)
    infer_instance
  haveI : ∀ c, LocallyOfFiniteType (Φ.C c).Y.str := fun c => by
    have := projProper _ _ _ (Φ.C c).Y.isProjOver
    infer_instance
  have hdX (C) : topologicalKrullDim ((nmodel z.Z).comp C).toBase.genFibre = d := hd C ▸ hdim C
  have hdY (c) : topologicalKrullDim (Φ.C c).Y.X = d := hd' c ▸ (Φ.C c).Y.topologicalKrullDim_eq
  have hov (k : Type) [Field k] (C) (c) (w : Sp k ⟶ ((nmodel z.Z).comp C).toBase.genFibre) (q : Sp k ⟶ (Φ.C c).Y.X)
      (h : Match L (Φ.C c) (w ≫ ι C) q) : w ≫ sX C = q ≫ (Φ.C c).Y.str := by
    obtain ⟨-, -, ⟨f, hf, hq⟩, -⟩ := UpperTheory.level_flag_compact_point L _ _ _ h
    haveI := mono_spMap_subtype (z.Z.i.c.V W)
    have h₁ : w ≫ sK C = spMap f := by
      rw [← cancel_mono (spMap (z.Z.i.c.V W).subtype), Category.assoc, ← hι, ← Category.assoc, hf]
    rw [hsX, ← (Φ.C c).π_str, reassoc_of% h₁, reassoc_of% hq]
  refine Exists.elim (UpperTheory.degree_matching_families F (i₀.c.F.val.toRingHom.comp e.toRingHom) (nmodel z.Z).Comp U.Comp
    (fun C => ((nmodel z.Z).comp C).toBase.genFibre) (fun c => (Φ.C c).Y.X) sX (fun c => (Φ.C c).Y.str) d
    (cov z * embDeg (incl z.Z)) (fun C => ι C ⁻¹' z.Z.opn) (fun c => (Φ.C c).π ⁻¹' Set.range T.jQ)
    (fun k _ C c w q => Match L (Φ.C c) (w ≫ ι C) q) hdX hdY (Nat.mul_pos (cov_pos z) hm0) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    fun β' hβ => ?_
  · intro C
    haveI := hopen C
    haveI : IsOpenImmersion ((nmodel z.Z).compι C) := inferInstanceAs (IsOpenImmersion (NModel.Comp.opens C).ι)
    haveI : IsOpenImmersion (ι C) := IsOpenImmersion.comp _ _
    have ho : IsOpen z.Z.opn := z.Z.cover ▸ isOpen_iUnion fun a => (z.Z.U a).1.isOpen
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := z.Z.dense.inter_open_nonempty _ (ι C).isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact (genericPoint_specializes y).mem_open (ho.preimage (ι C).continuous) hy
  · intro c
    have h := congrArg (fun g => g (closedPoint _)) (Φ.C c).y0_x
    refine ⟨_, h.trans ?_⟩
    exact congrArg (Φ.C c).π Scheme.fromSpecStalk_closedPoint
  · intro k _ C c w q h
    obtain ⟨h₁, h₂, -⟩ := UpperTheory.level_flag_compact_point L _ _ _ h
    exact ⟨hov k C c w q h, h₁, h₂⟩
  · intro k _ C w hw
    exact UpperTheory.level_unfolding_flag Φ L (w ≫ ι C) hw
  · intro k _ C c c' w q q' h h'
    exact UpperTheory.level_unfolding_metric Φ L z.full _ _ _ _ _ h h'
  · intro k k' _ _ ψ C c w q h
    rw [Category.assoc]
    exact (UpperTheory.level_flag_compact_point L _ _ _ h).2.2.2 k' ψ
  · intro c q hq hQ
    haveI := T.jQ_open
    obtain ⟨y, hy⟩ : ∃ y : Sp ℂ ⟶ (Xo i₀.l).XF i₀.c, q ≫ (Φ.C c).π = y ≫ T.jQ :=
      ⟨IsOpenImmersion.lift T.jQ (q ≫ (Φ.C c).π) (by
        rintro _ ⟨a, rfl⟩
        rw [Subsingleton.elim (α := PrimeSpectrum ℂ) a (closedPoint ℂ)]
        exact hQ), (IsOpenImmersion.lift_fac _ _ _).symm⟩
    have hy' : y ≫ pullback.snd _ _ = spMap i₀.c.F.val.toRingHom := by
      haveI : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
      rw [← cancel_mono (spMap e.toRingHom), ← T.jQ_over, GlobalTheory.ModelRelProbe.spMap_comp, ← hq, ← (Φ.C c).π_str,
        reassoc_of% hy]
      simp only [Category.assoc]
    obtain ⟨e₁⟩ := UpperTheory.level_flag_multiplicity L (Φ.C c) z.full q y hy
    have h₂ := UpperTheory.level_point_count L hpq ⟨y, hy'⟩
    obtain ⟨inj, sur⟩ := UpperTheory.points_generic_fibre_components _ (nmodel z.Z) ℂ
    refine Eq.trans (Nat.card_eq_of_bijective (fun x => (⟨x.1.2 ≫ ι x.1.1, x.2⟩ : {w // Match L (Φ.C c) w q}))
      ⟨fun x y hxy => Subtype.ext (inj (congrArg Subtype.val hxy)), fun w => ?_⟩) ((Nat.card_congr e₁).trans h₂)
    obtain ⟨C, w', hw'⟩ := sur w.1 (opn_subset_gen hp hW (UpperTheory.level_flag_compact_point L _ _ _ w.2).1)
    exact ⟨⟨⟨C, w'⟩, hw' ▸ w.2⟩, Subtype.ext hw'⟩
  · obtain ⟨θ, hθ, hθ0, hsum⟩ := hβ
    have key (C) : num (sX C) (fun t => pull (ι C) (m t • (z.line false _ (x t) (letterOf_self (x t))).L.cls)) =
        (embDeg (θ C) : ℤ) * num (Φ.C (β' C)).Y.str fun t => toPic (m t • (Φ.C (β' C)).gr (x t).1 (x t).2) := by
      choose D hD hD' using fun t => UpperTheory.level_flag_prime hE hp hW z.full L (Φ.C (β' C)) _ (ι C) (sK C) (hι C)
        (UpperTheory.functionField_essFiniteType_int F _ (sX C)) (θ C) (hθ C) (x t) (z.line false _ (x t) (letterOf_self (x t)))
      have h := UpperTheory.intersection_numbers_agree_model F _ _ (sX C) (Φ.C (β' C)).Y.str (θ C) d (hpX C) (Φ.C (β' C)).Y.isProjOver (hdX C) (hdY _)
        ((Category.assoc _ _ _).symm.trans (hov _ _ _ _ _ (hθ C)).symm) (hθ0 C) (fun t => m t • D t)
        (fun t => m t • (Φ.C (β' C)).gr (x t).1 (x t).2) fun t => by
          rcases hm t with h | h <;> rw [h]
          · simpa only [one_smul] using hD' t
          · simpa only [neg_smul, one_smul] using (hD' t).neg
      refine Eq.trans ?_ (h.trans (congrArg _ (num_eq _ fun t => isLB_toLB _).symm))
      refine Eq.trans (congrArg _ (funext fun t => ?_)) (num_eq _ fun t => isLB_toLB _)
      rw [← toPic_apply, map_zsmul, map_zsmul, hD]
    have key' (C) := (num_comp _ (hm' C ▸ hm0) _ (hproj C) _).symm.trans (key C)
    simp only [hm'] at key'
    refine mul_left_cancel₀ (Nat.cast_ne_zero.2 hm0.ne' : (embDeg (incl z.Z) : ℤ) ≠ 0) ?_
    rw [Finset.mul_sum, Finset.sum_congr rfl fun C _ => key' C, ← Finset.sum_fiberwise (g := β'), ← mul_assoc,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_mul, mul_comm (embDeg _), ← hsum j, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl

end Free

theorem mem_span_prod {σ : Type} {d : ℕ} {P : MvPolynomial σ ℚ} (hP : P.IsHomogeneous d) :
    P ∈ Submodule.span ℚ (Set.range fun s : Fin d → σ => ∏ i, (MvPolynomial.X (s i) : MvPolynomial σ ℚ)) := by
  classical
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hl : m.toMultiset.toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]
    simp only [smul_eq_mul, mul_one, Pi.one_apply]
    rfl
  subst hl
  have e : MvPolynomial.monomial m (P.coeff m) =
      P.coeff m • ∏ i, (MvPolynomial.X (m.toMultiset.toList.get i) : MvPolynomial σ ℚ) := by
    rw [← List.prod_ofFn, ← Function.comp_def MvPolynomial.X, ← List.map_ofFn, List.ofFn_get, Multiset.prod_map_toList,
      Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add]),
      MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem sum_ext_prod {σ I J A : Type} [Fintype I] [Fintype J] [CommRing A] [Algebra ℚ A] (f : σ → A)
    (Λ : I → A →ₗ[ℚ] ℚ) (Ψ : J → MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (a : ℝ) {d : ℕ}
    (h : ∀ s : Fin d → σ, ((∑ i, Λ i (∏ t, f (s t)) : ℚ) : ℝ) = a * ∑ j, Ψ j (∏ t, MvPolynomial.X (s t)))
    {P : MvPolynomial σ ℚ} (hP : P.IsHomogeneous d) :
    ((∑ i, Λ i (MvPolynomial.aeval f P) : ℚ) : ℝ) = a * ∑ j, Ψ j (MvPolynomial.map (algebraMap ℚ ℝ) P) := by
  refine Submodule.span_induction (fun Q hQ => ?_) ?_ (fun Q Q' _ _ h₁ h₂ => ?_) (fun a Q _ h₁ => ?_) (mem_span_prod hP)
  · obtain ⟨s, rfl⟩ := hQ
    simpa only [map_prod, MvPolynomial.aeval_X, MvPolynomial.map_X] using h s
  · simp
  · simp only [map_add, Finset.sum_add_distrib, Rat.cast_add, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  · have e : MvPolynomial.map (algebraMap ℚ ℝ) (a • Q) = (a : ℝ) • MvPolynomial.map (algebraMap ℚ ℝ) Q := by
      simp [MvPolynomial.smul_eq_C_mul]
    simp only [e, map_smul, smul_eq_mul, ← Finset.mul_sum, Rat.cast_mul] at h₁ ⊢
    rw [h₁, mul_left_comm]

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

theorem sum_interPoly (hP : GlobalTheory.CovTop.Hypotheses2) (D : D7) (O : Setup D) (Q : MvPolynomial (Rt D.what₂.Tau O.N) ℝ)
    (hQ : Q.IsHomogeneous (dimFl D.what₂.Tau O.N)) :
    ∑ c, (O.var c).interPoly (fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x)) Q = O.Y.chern Q := by
  classical
  have hM : GlobalTheory.Published.MumfordProportionality := (GlobalTheory.T.stronger_published_hypotheses_imply hP).p16
  have one (c : O.s.Comp) : (O.var c).interPoly (fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x)) Q =
      (O.s.cx O.L O.B O.fl).volC c * degFlL D.what₂.Tau O.N Q := by
    have he : (O.var c).dim = dimFl D.what₂.Tau O.N := O.dim_eq c
    have key := GlobalTheory.T.polynomial_power_eq_of_integral_points (dimFl D.what₂.Tau O.N) ((O.var c).interPoly fun x : Rt D.what₂.Tau O.N =>
        divOf (O.Φ.C c) (O.ex x)) ((O.s.cx O.L O.B O.fl).volC c • degFlL D.what₂.Tau O.N)
      (fun a => by
        have := GlobalTheory.CompPropObj.interPoly_int hM O c fun τ i => -a (τ, i)
        simp only [neg_neg, he] at this
        refine this.trans ?_
        have hl : linRoot (fun τ i => ((-a (τ, i) : ℤ) : ℝ)) = ∑ x, C ((a x : ℤ) : ℝ) * X x := by
          simp [linRoot, Finset.sum_neg_distrib]
        show _ * degFl _ _ (linRoot _ ^ dimFl _ _) = _ * (degFlL D.what₂.Tau O.N _)
        rw [hl]
        erw [degFlL_apply]
        try rfl)
    have h := GlobalTheory.PowLinSpan.homog_kill (((O.var c).interPoly fun x : Rt D.what₂.Tau O.N =>
        divOf (O.Φ.C c) (O.ex x)) - (O.s.cx O.L O.B O.fl).volC c • degFlL D.what₂.Tau O.N) (dimFl D.what₂.Tau O.N)
      (MvPolynomial.funext fun u => by
        rw [GlobalTheory.PowLinSpan.eval_polOf, map_zero, LinearMap.sub_apply, sub_eq_zero]
        exact key u) Q hQ
    exact sub_eq_zero.1 h
  rw [Finset.sum_congr rfl fun c _ => one c, ← Finset.sum_mul]
  change _ = O.Y.vol * degFlL D.what₂.Tau O.N Q
  rfl

theorem exists_letter {D : D7} (O : Setup D) (x : Rt D.what₂.Tau O.N) : ∃ (ℓ : Letter O.S.Dw) (m : ℤ), (m = 1 ∨ m = -1) ∧
    O.ex x = expo O.S.Dw (Finsupp.single (fun _ => false, none, .inl (ℓ.1, ℓ.2)) m) ∧
    ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt O.S O.κ hp hW),
      (z.rootLB false (tauEmb D x.1) x.2).cls = m • (z.line false _ ℓ (letterOf_self ℓ)).L.cls := by
  have h₁ : O.S.Dw.mult (tauEmb D x.1) = O.S.Dw.p := if_pos (O.A.cm x.1)
  have h₂ := GlobalTheory.Proof.LetterConjugation.mult_add O.S.Dw (tauEmb D x.1)
  have h₃ := O.S.rank_eq
  have h₄ := x.2.2
  by_cases h : (x.2 : ℕ) < O.S.Dw.p
  · refine ⟨⟨tauEmb D x.1, ⟨x.2, h₁ ▸ h⟩⟩, 1, .inl rfl, congrArg _ (if_pos h), fun p hp W hW z => ?_⟩
    rw [admitted.rootLB, if_pos h, one_smul]
    exact congrArg FinLB.cls (z.stepLB_of_some false (letterOf_self ⟨tauEmb D x.1, ⟨x.2, h₁ ▸ h⟩⟩))
  · have h₅ : O.S.Dw.p + O.S.Dw.q - 1 - x.2 < O.S.Dw.mult (conjEmb (tauEmb D x.1)) := by omega
    refine ⟨⟨conjEmb (tauEmb D x.1), ⟨_, h₅⟩⟩, -1, .inr rfl, congrArg _ (if_neg h), fun p hp W hW z => ?_⟩
    rw [admitted.rootLB, if_neg h, neg_smul, one_smul, FinLB.cls_dual]
    exact congrArg (fun L : FinLB _ => -L.cls) (z.stepLB_of_some false (letterOf_self ⟨conjEmb (tauEmb D x.1), ⟨_, h₅⟩⟩))

set_option maxHeartbeats 1600000 in

theorem geoAll (hP : GlobalTheory.CovTop.Hypotheses2) (D : D7) (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ)
    (hW : (p : ℂ) ∈ W.nonunits) (jc : KW p →+* ℂ) (z : AdmAt O.S O.κ (Fact.out : p.Prime) hW)
    (P : MvPolynomial (Rt D.what₂.Tau O.N) ℚ) (h : P.IsHomogeneous (dimFl D.what₂.Tau O.N)) :
    haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
    ((∑ C ∈ Finset.univ.filter (fun C : (nmodel z.Z).Comp => ((nmodel z.Z).comp C).relDim = dimFl D.what₂.Tau O.N),
      ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C)
        (aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) P)) : ℚ) : ℝ) =
      ((mdlOf z jc).cov : ℝ) * O.Y.chern (toR P) := by
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  have hd := RelDim.relDim_comp D O.A O.N O.j O.S O.κ p Fact.out W hW z
  refine Eq.trans ?_ (congrArg (((mdlOf z jc).cov : ℝ) * ·) (sum_interPoly hP D O (toR P) (h.map _)))
  simp only [hd, Finset.filter_true]
  refine sum_ext_prod (A := PicSym (nmodel z.Z).X) (fun x : Rt D.what₂.Tau O.N => (z.rootLB false (tauEmb D x.1) x.2).c1)
    (fun C => ((nmodel z.Z).comp C).toBase.fibreDeg ∘ₗ (picSymPull ((nmodel z.Z).compι C)).toLinearMap)
    (fun c => (O.var c).interPoly fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x)) (cov z) (fun s => ?_) h
  choose ℓ m hm hex hcl using exists_letter O
  have key := sum_fibre hP.p22 Fact.out hW ((one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge) z O.Φ hd O.dim_eq
    (fun t => ℓ (s t)) (fun t => m (s t)) fun t => hm (s t)
  have e₁ (C : (nmodel z.Z).Comp) : (((nmodel z.Z).comp C).toBase.fibreDeg ∘ₗ
      (picSymPull ((nmodel z.Z).compι C)).toLinearMap) (∏ t, (z.rootLB false (tauEmb D (s t).1) (s t).2).c1) =
      (num ((nmodel z.Z).comp C).toBase.genFibreStr fun t =>
        pull (((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C)
          (m (s t) • (z.line false _ (ℓ (s t)) (letterOf_self (ℓ (s t)))).L.cls) : ℤ) := by
    let M (t) : FinLB ((nmodel z.Z).comp C).X :=
      FinLB.pull (z.rootLB false (tauEmb D (s t).1) (s t).2) ((nmodel z.Z).compι C)
    have e : picSymPull ((nmodel z.Z).compι C) (∏ t, (z.rootLB false (tauEmb D (s t).1) (s t).2).c1) =
        ∏ t, c1 (M t).lb (M t).isLB :=
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun t _ => FinLB.pullback_firstChern _ _)
    refine (congrArg ((nmodel z.Z).comp C).toBase.fibreDeg e).trans ?_
    rw [Vert.Model.Hom.fibreDeg_prod, if_pos ((Fintype.card_fin _).trans
      (Vert.Model.relDim_toBase.trans (hd C)).symm)]
    refine congrArg _ ((num_eq _ fun t => LB.isLB_pull (M t).isLB _).symm.trans (congrArg _ (funext fun t => ?_)))
    rw [cls_pull (M t).isLB, pull_comp, ← hcl]
    exact congrArg _ (FinLB.cls_pull _ _)
  have e₂ (c : O.s.Comp) : (O.var c).interPoly (fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x))
      (∏ i, X (s i)) =
      (num (O.Φ.C c).Y.str fun t => toPic (m (s t) • (O.Φ.C c).gr (ℓ (s t)).1 (ℓ (s t)).2) : ℤ) := by
    have hc := O.dim_eq c
    simp only [← divOf_single (O.Φ.C c) (fun _ => false) none, ← hex]
    clear key e₁
    revert s
    rw [← hc]
    intro s
    rw [ProjVar.Var.interPoly_prod]
    exact congrArg _ (num_eq _ fun t => isLB_toLB _).symm
  rw [Finset.sum_congr rfl fun C _ => e₁ C, Finset.sum_congr rfl fun c _ => e₂ c]
  exact_mod_cast key

end GlobalTheory.ConsGeo.GenDeg
