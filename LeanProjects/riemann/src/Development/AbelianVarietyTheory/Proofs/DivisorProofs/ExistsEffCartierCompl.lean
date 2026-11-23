import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFiel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoExponentDivisorPullbackFlagCoverStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompProport

open scoped ENNReal in

theorem growth_eq_of_tendsto (D : ℕ) (r : ℕ → ℕ) {c : ℝ}
    (h : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial))) :
    GlobalTheory.CompHt.growth D (fun m => (r m : ℕ∞)) = ENNReal.ofReal c := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal ((D.factorial : ℝ) * ((r m : ℝ) / (m : ℝ) ^ D))) atTop
      (nhds (ENNReal.ofReal c)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := h.const_mul (D.factorial : ℝ)
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  refine (Tendsto.limsup_eq ?_)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [ENat.toENNReal_coe, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast]

theorem exists_effCartier_compl (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (hU : Dense (U : Set X))
    (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal U.compl)) :
    ∃ BD : EffCartierData X, ∀ x, x ∈ BD.idealSheaf.support ↔ x ∉ U := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq (I := Scheme.IdealSheafData.vanishingIdeal U.compl) fun y => by
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := h y
    refine ⟨W, _, hy, mem_nonZeroDivisors_iff_right.2 fun g hg => ?_, hI⟩
    have h1 : X.basicOpen g ⊓ X.basicOpen (∏ i ∈ J, f i) = ⊥ := by
      rw [← Scheme.basicOpen_mul, hg, Scheme.basicOpen_zero]
    rw [← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨z, hz, hzU⟩ := hU.inter_open_nonempty _ (X.basicOpen g).isOpen ((Opens.ne_bot_iff_nonempty _).1 hne)
    have h2 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := Scheme.IdealSheafData.vanishingIdeal U.compl)
      (U := W) (X.basicOpen_le g hz)
    rw [hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, ← SetLike.mem_coe,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at h2
    have h3 : z ∈ X.basicOpen (∏ i ∈ J, f i) := not_not.1 fun h3 => h2.2 h3 hzU
    exact h1.le (show z ∈ _ ⊓ _ from ⟨hz, h3⟩)
  refine ⟨D, fun x => ?_⟩
  rw [hD, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

theorem tendsto_zero_of_dim_lt (h : GlobalTheory.Published.NefRiemannRoch) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) {D : ℕ} (hD : topologicalKrullDim X + 1 ≤ D) {L : LB X} (hL : IsNef k L) :
    Tendsto (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) / (m : ℝ) ^ D) atTop (nhds 0) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine tendsto_const_nhds.congr fun m => ?_
    have : lbH0 k (lbPow L m) = 0 := by
      by_contra h0
      obtain ⟨s, hs⟩ := lineBundleHasNonzeroSection_of_globalSectionsDim_pos (Nat.pos_of_ne_zero h0)
      refine hs (DVR.SecOps.sec_ext fun i => fun_ext_ger fun y _ => (hX.false y).elim)
    simp [this]
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = d := by
      have h0 : topologicalKrullDim X ≠ ⊥ := fun h => (QCoh.topologicalKrullDim_eq_bot_iff.1 h).elim (Classical.arbitrary X)
      obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 h0
      rw [← ha] at hD ⊢
      induction a using ENat.recTopCoe with
      | top => exact absurd hD (by
          intro h
          have h' : (⊤ : ℕ∞) + 1 ≤ (D : ℕ∞) := by exact_mod_cast h
          simp at h')
      | coe a => exact ⟨a, rfl⟩
    rw [hd] at hD
    have hlt : d + 1 ≤ D := by exact_mod_cast hD
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hlt
    have h2 : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ (e + 1)) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (e + 1)
    have := (h.tendsto hp hd hL).mul h2
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    rw [inv_pow, ← div_eq_mul_inv, div_div, ← pow_add]
    congr 2
    omega

theorem growth_vanishing (hN : GlobalTheory.Published.NefNumerics) (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hp : IsProjOver p) (hD : topologicalKrullDim X = D) (B : Closeds X) (hB : genericPoint X ∉ B) (L : LB X) (hL : L.IsLB)
    (hn : letI := algebraΓOfHom p; IsNef k L) (M : ℕ → LB X) (hM : ∀ m, (M m).IsLB) (e : ∀ m, cls (M m) (hM m) = m • cls L hL)
    (V : ∀ m, Submodule k (H0 p (M m) ⊤))
    (hV : ∀ m s, s ∈ V m ↔ ∀ y ∈ B, ∀ i hi, H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal _) :
    GlobalTheory.CompHt.growth D (fun m => Cardinal.toENat (Module.rank k (V m))) =
      ENNReal.ofReal ((letI := algebraΓOfHom p; topSelfIntersection k L D : ℤ) : ℝ) := by
  letI := algebraΓOfHom p
  let i := redι B
  letI := algebraΓOfHom (i ≫ p)
  have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal B
  have hs : strHom k X = p := strHom_eq fun _ => rfl
  have hs' : strHom k _ = i ≫ p := strHom_eq fun _ => rfl
  have hp' : IsProjOver (i ≫ p) := by
    obtain ⟨n, j, hj, hj'⟩ := hp
    exact ⟨n, i ≫ j, inferInstance, by rw [Category.assoc, hj']⟩
  have hfin : ∀ {T : Scheme.{0}} (q : T ⟶ Sp k) (N : LB T), IsProjOver q → N.IsLB → Module.Finite k (H0 q N ⊤) := by
    intro T q N hq hN
    letI := algebraΓOfHom q
    have := finite_coh_zero_twist_of_isProjOver (k := k) (f := q) (fun _ => rfl) hq hN
    have e (c : k) : algebraMap k Γ(T, ⊤) c = DVR.FlatBC.algX q ⊤ c := by
      change q.appTop _ = _
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    refine Module.Finite.of_surjective
      ({ toFun := fun x => H0.ofSec q ⊤ (cohZeroTwistEquiv N x)
         map_add' := fun x y => by rw [map_add, map_add]
         map_smul' := fun a x => ?_ } : coh (twist (QCoh.structureModule T) N) 0 →ₗ[k] H0 q N ⊤)
      (H0.bijective_ofSec_top.2.comp (cohZeroTwistEquiv N).surjective)
    rw [← algebraMap_smul Γ(T, ⊤) a x, map_smul, e, H0.ofSec_smul]
    rfl
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal B).subscheme + 1 ≤ D := by
    rw [topologicalKrullDim_red, ← hD]
    exact (topologicalKrullDim_add_one_le B.isClosed isClosed_univ fun x _ =>
      ⟨genericPoint X, trivial, hB, genericPoint_specializes x⟩).trans (topologicalKrullDim_subspace_le _ _)
  have hn' : IsNef k (L.pull i) := hn.pull_of_isClosedImmersion i fun _ => rfl
  have t1 := hN.2.2.tendsto (by rw [hs]; exact hp) hD hn
  have t2 := tendsto_zero_of_dim_lt hN.2.2 (by rw [hs']; exact hp') hdim hn'
  have key : ∀ m, Module.finrank k (V m) ≤ lbH0 k (lbPow L m) ∧
      lbH0 k (lbPow L m) ≤ Module.finrank k (V m) + lbH0 k (lbPow (L.pull i) m) := fun m => by
    have := hfin p _ hp (hM m)
    have := hfin (i ≫ p) _ hp' (LB.isLB_pull (hM m) i)
    rw [← lineBundleGlobalSectionsDim_congr_picardClass (hM m) (isLB_lbPow hL m) (by rw [e, cls_lbPow hL]),
      ← lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (hM m) i) (isLB_lbPow hn'.isLB m)
        (by rw [cls_pull (hM m), e, cls_lbPow hn'.isLB, cls_pull hL, map_nsmul]),
      ← H0.finrank_top p, ← H0.finrank_top (i ≫ p)]
    refine ⟨Submodule.finrank_le _, ?_⟩
    let φ : H0 p (M m) ⊤ →ₗ[k] H0 (i ≫ p) ((M m).pull i) ⊤ := H0.pull i le_top
    rw [← φ.finrank_range_add_finrank_ker, add_comm]
    refine add_le_add (Submodule.finrank_mono fun s hs => (hV m s).2 fun y hy j hj hu => ?_) (Submodule.finrank_le _)
    obtain ⟨z, rfl⟩ : y ∈ Set.range i := (range_redι B).ge hy
    have h1 := H0.germ_pull (p := p) (O := ⊤) (W := ⊤) i le_top (pIdx (M m) i j) z (memTop z) (mem_pIdx.2 hj) s
    rw [show H0.pull i le_top s = 0 from hs, map_zero] at h1
    exact not_isUnit_zero (h1 ▸ hu.map (i.stalkMap z).hom)
  have t3 : Tendsto (fun m : ℕ => (Module.finrank k (V m) : ℝ) / (m : ℝ) ^ D) atTop
      (nhds ((topSelfIntersection k L D : ℝ) / D.factorial)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using t1.sub t2) t1 (fun m => ?_) fun m => ?_
    · dsimp only
      rw [← sub_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : (lbH0 k (lbPow L m) : ℝ) ≤ Module.finrank k (V m) + lbH0 k (lbPow (L.pull i) m) := by
        exact_mod_cast (key m).2
      linarith
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (key m).1) (by positivity)
  rw [← growth_eq_of_tendsto D _ t3]
  congr 1
  funext m
  have := hfin p _ hp (hM m)
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]

section Flag

open GlobalTheory.VarFlag
open GlobalTheory.ShFam (EigFrame FlagCpt FlagTor)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal HasToricChart)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_iso (T : TorFlag Xo c) (Z : Comp Xo c) (B : Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen T.Y)
    (hB : ∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧
      j i ≫ genStr T.Y ≫ spMap (RingEquiv.refl c.F).toRingHom = (B i).str ∧ ∀ p ∈ i.1, T.Y.jQ p ∈ Set.range (j i))
    (hcov : ∀ z : gen T.Y, ∃! i, z ∈ Set.range (j i)) (C : FlagCpt T.Y (RingEquiv.refl c.F)) (f : C.Y.X ⟶ (B Z).X)
    (hπ : C.π = f ≫ j Z)
    (hl : ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen T.Y) (x' : Sp K ⟶ (B Z).X), x' ≫ j Z = x →
      x ≫ genStr T.Y = spMap χ → ∀ g : EigFrame T.Y χ (x ≫ genι T.Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) :
    ∃ h : Y₀ T.X Z ⟶ C.Y.X, IsIso h ∧ h ≫ C.π ≫ genι T.Y = inc₀ T.X Z ≫ T.X.π ∧ h ≫ C.Y.str = str₀ T.X Z ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), Rel T.X.F C (z ≫ inc₀ T.X Z) (z ≫ h) := by
  have := (hB Z).1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := GlobalTheory.T.flagBundlePointFramesTriangular_component C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR
  have hiso := GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine ⟨h, this, hh, ?_, hR⟩
  rw [← hps, ← Category.assoc, hh, Category.assoc]

theorem exists_flagTor (T : TorFlag Xo c) (hF : FnAlgClosed Xo c) {σ : c.F →+* ℂ} {N : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ N)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ (Φ : FlagTor T.Y (RingEquiv.refl c.F) U) (q : U.Comp ≃ Comp Xo c),
      (∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1) ∧
      ∀ k, ∃ h : Y₀ T.X (q k) ⟶ (Φ.C k).Y.X, IsIso h ∧ h ≫ (Φ.C k).π ≫ genι T.Y = inc₀ T.X (q k) ≫ T.X.π ∧
        h ≫ (Φ.C k).Y.str = str₀ T.X (q k) ∧
        ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X (q k)), Rel T.X.F (Φ.C k) (z ≫ inc₀ T.X (q k)) (z ≫ h) := by
  have hsm := smooth_gen T.smooth
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU (fun k => GlobalTheory.CompBij.frames_nonempty _) hF
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have key := fun i : U.Comp =>
    haveI := (hB (q i)).1
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B (q i)) (j (q i)) (hB (q i)).2.2.1
  choose C f hπ hdim hl using key
  have lift : ∀ (K : Type) [Field K] (x : Sp K ⟶ gen T.Y) (i : Comp Xo c),
      x (IsLocalRing.closedPoint K) ∈ Set.range (j i) → ∃ x' : Sp K ⟶ (B i).X, x' ≫ j i = x := fun K _ x i h => by
    have := (hB i).1
    refine ⟨IsOpenImmersion.lift (j i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨w, rfl⟩
    rwa [show w = IsLocalRing.closedPoint K from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  refine ⟨⟨C, fun k => ?_, fun K _ _ χ x hx g => ?_, fun i x s => ?_⟩, q, hq,
    fun k => exists_iso T (q k) B j hB hcov (C k) (f k) (hπ k) (hl k)⟩
  · rw [hdim, (hB _).2.1, GlobalTheory.T.flag_space_dimension_eq_sum_choose E H Dw, hU.1]
  · obtain ⟨i₀, hi, hi'⟩ := hcov (x (IsLocalRing.closedPoint K))
    obtain ⟨i, rfl⟩ := q.surjective i₀
    obtain ⟨x', hx'⟩ := lift K x _ hi
    obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hl i K χ x x' hx' hx g
    refine ⟨⟨i, p⟩, ⟨by rw [hπ, ← Category.assoc, hp1, hx'], hp2⟩, ?_⟩
    rintro ⟨i', p'⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    rw [hπ, ← Category.assoc] at h1
    obtain rfl : i' = i := q.injective (hi' _ ⟨(p' ≫ f i') (IsLocalRing.closedPoint K), by
      rw [← h1]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩)
    have := (hB (q i')).1
    rw [hp3 p' ⟨(cancel_mono (j (q i'))).1 (h1.trans hx'.symm), h2⟩]
  · let x₀ : Sp ℂ ⟶ gen T.Y := (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un i x) ≫ T.Y.jQ :)
    have hx₀ : x₀ ≫ genStr T.Y = spMap σ :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) T.Y.jQ_over).trans (pullback.lift_snd _ _ _))
    obtain ⟨x', hx'⟩ := lift ℂ x₀ (q i) ((hB _).2.2.2 _ (hq i x _))
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ T.Y _ _ x₀ hx₀
    obtain ⟨p, ⟨hp1, -⟩, -⟩ := hl i _ _ x₀ x' hx' hx₀ g
    have : p ≫ (C i).π = x₀ := by rw [hπ, ← Category.assoc, hp1, hx']
    exact ⟨p s, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp ℂ ⟶ gen T.Y => t s) this)⟩

theorem topSelf_eq_inter (T : TorFlag Xo c) (Z : Comp Xo c) (C : FlagCpt T.Y (RingEquiv.refl c.F)) (h : Y₀ T.X Z ⟶ C.Y.X)
    [IsIso h] (hh : h ≫ C.π ≫ genι T.Y = inc₀ T.X Z ≫ T.X.π) (hs : h ≫ C.Y.str = str₀ T.X Z)
    (hR : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), Rel T.X.F C (z ≫ inc₀ T.X Z) (z ≫ h)) (la : AllWt.Weight Dw) :
    (letI := algebraΓOfHom (str₀ T.X Z); topSelfIntersection c.F (L₀ T.X Z la) C.Y.dim) = C.Y.inter fun _ => C.Lw la := by
  letI := algebraΓOfHom (str₀ T.X Z)
  have hL := isLB_L₀ T.X Z la
  have hL' := T.X.F.isLB_LL (AllWt.exOf Dw la 0)
  have e := GlobalTheory.T.lineBundleIso_exponentDivisor_pullback_flagCover T.X C (inv h ≫ inc₀ T.X Z) (by rw [Category.assoc, ← hh, IsIso.inv_hom_id_assoc])
    (fun K _ p => by simpa using hR K (p ≫ inv h)) (AllWt.exOf Dw la 0) rfl
  have e' : topSelfIntersection c.F (C.Y.lb (C.Lw la)) C.Y.dim = topSelfIntersection c.F ((L₀ T.X Z la).pull (inv h)) C.Y.dim :=
    interNum_congr_cls _ _ (fun _ => Cartier.isLB_toLB _) (fun _ => LB.isLB_pull hL _) fun _ => by
      rw [cls_pull hL, cls_pull hL', ← pull_comp, ← cls_pull hL' _ (LB.isLB_pull hL' _)]
      exact (cls_eq_iff _ _).2 e
  rw [GlobalTheory.ProjVar.Var.inter_const, e', ← interNumOn_const_eq_topSelf (f := inv h) (fun r => ?_) hL]
  · have := interNumOn_comp_of_isIso c.F (inv h) (𝟙 _) (fun _ : Fin C.Y.dim => L₀ T.X Z la)
    rw [Category.comp_id, interNumOn_id] at this
    exact this.symm
  · rw [C.Y.algebraMap_Γ, show C.Y.str = inv h ≫ str₀ T.X Z by rw [← hs, IsIso.inv_hom_id_assoc]]
    rfl

open Classical in

theorem topSelf_eq_covol (hM : GlobalTheory.Published.MumfordProportionality) (T : TorFlag Xo c) (hc : ∀ x ∈ genBd T.Y, HasToricChart T.Y x)
    (hF : FnAlgClosed Xo c) {σ : c.F →+* ℂ} {N : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ N)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ q : U.Comp ≃ Comp Xo c, (∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1) ∧
      ∀ k, IsIntegral (Y₀ T.X (q k)) ∧ topologicalKrullDim (Y₀ T.X (q k)) = CompHt.dimFlag Dw ∧ ∀ la : AllWt.Weight Dw,
        ((letI := algebraΓOfHom (str₀ T.X (q k)); topSelfIntersection c.F (L₀ T.X (q k) la) (CompHt.dimFlag Dw) : ℤ) : ℝ) =
          GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (AllWt.Psi H) (Dw.p + Dw.q) fun τ i => (la τ i : ℝ) := by
  obtain rfl : N = Dw.p + Dw.q := hU.1
  obtain ⟨Φ, q, hq, hΦ⟩ := exists_flagTor T hF U hσ hU
  have : IsReduced T.Y.X :=
    have : ∀ x : T.Y.X, _root_.IsReduced (T.Y.X.presheaf.stalk x) := fun x => have := (T.Y.normal x).1; inferInstance
    isReduced_of_isReduced_stalk _
  obtain ⟨BD, hBD⟩ := exists_effCartier_compl T.Y.X (LogKS.interior T.Y) (LogKS.dense_interior T.Y) T.snc
  have hab : ∀ x, x ∈ BD.idealSheaf.support ↔ x ∉ abLocus T.Y.t.G := fun x => by
    rw [hBD, ← LogKS.coe_interior]; rfl
  let T' := GlobalTheory.TorRef.selfTor T.Y (smooth_gen T.smooth) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) hc BD (fun x hx => (hab x).1 hx)
    (fun x hx => (hab _).2 (GlobalTheory.Toroidal.mem_genBd_iff.1 hx)) 1 one_pos
  refine ⟨q, hq, fun k => ?_⟩
  obtain ⟨h, _, h1, h2, h3⟩ := hΦ k
  have hd : (Φ.C k).Y.dim = CompHt.dimFlag Dw := by
    rw [Φ.dim_eq, dimFlag_eq, FlagTan.dimFlag, Nat.choose_two_right]
  refine ⟨(have : Nonempty (Y₀ T.X (q k)) := ⟨inv h (genericPoint _)⟩; isIntegral_of_isOpenImmersion h), ?_, fun la => ?_⟩
  · rw [← hd, ← (Φ.C k).Y.topologicalKrullDim_eq]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  · rw [← hd, topSelf_eq_inter T _ _ h h1 h2 h3]
    refine (hM E H Dw l Xo c _ _ _ T' _ _ σ U hσ hU Φ k la).trans ?_
    exact congrArg (fun i => _ * @Formalism.DegreeFormula.flagDeg (AllWt.Psi H) i _ (Dw.p + Dw.q) fun τ i => (la τ i : ℝ))
      (Subsingleton.elim _ _)

end Flag

section Good

open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegCmp
open GlobalTheory.Toroidal (genBd HasToricChart)

theorem gapGe_of_strictAnti {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {la : AllWt.Weight Dw} (h : ∀ τ, StrictAnti (la τ)) : GapGe 0 la := fun τ k hk => by
  rw [gap, dif_pos hk]
  exact sub_nonneg.2 (h τ (Fin.mk_lt_mk.2 k.lt_succ_self)).le

theorem growthOn_eq_topSelf (hP : Hypotheses₂) (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    [IsIntegral (Y₀ TF.X Z)] (hd : topologicalKrullDim (Y₀ TF.X Z) = CompHt.dimFlag (T.Q.Dw j))
    {la : AllWt.Weight (T.Q.Dw j)} (hla : ∀ τ, StrictAnti (la τ)) :
    CompHt.growthOn Y.U Z (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
      ((letI := algebraΓOfHom (str₀ TF.X Z); topSelfIntersection Y.d.c₂.F (L₀ TF.X Z la) (CompHt.dimFlag (T.Q.Dw j)) : ℤ) : ℝ) := by
  have hg : genericPoint (Y₀ TF.X Z) ∉ bd₀ TF.X Z := fun h => by
    obtain ⟨y, hy⟩ := (dense_U₀ TF.X Z).nonempty
    exact h ((genericPoint_specializes y).mem_open (U₀ TF.X Z).isOpen hy)
  have hc : ∀ m : ℕ, cls (L₀ TF.X Z (m • la)) (isLB_L₀ _ _ _) = m • cls (L₀ TF.X Z la) (isLB_L₀ _ _ _) := fun m => by
    have a := cls_common_add (common₀ TF.X Z)
    induction m with
    | zero =>
      have := a 0 0
      simp only [add_zero] at this
      rw [zero_nsmul, zero_nsmul]
      exact left_eq_add.1 this
    | succ m ih => rw [succ_nsmul, succ_nsmul, ← ih]; exact a _ _
  rw [← growth_vanishing hN _ _ (str₀ TF.X Z) _ (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo).2.1 hd _ hg _
    (isLB_L₀ _ _ la) (GlobalTheory.T.nef_line_bundle_weight_gap hP hN hL _ _ _ _ _ _ TF Z hY.geo la (gapGe_of_strictAnti hla)) _ _ hc
    (fun m => vanBd TF.X Z (m • la)) fun _ _ => Iff.rfl, CompHt.growthOn]
  congr 1
  funext m
  have h1 := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace D T j Y e o hY hf Z TF (m • la)
  have h2 := le_antisymm h1.space_le (vanBd_le_space D T j Y e o hY hf Z TF (m • la))
  rw [CompHt.nsmul_wtOf, smul_zero, ← h2]
  exact congrArg _ h1.equiv.rank_eq

theorem growthOn_eq_covol (hP : Hypotheses₂) (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k (la : AllWt.Weight (T.Q.Dw j)), (∀ τ, StrictAnti (la τ)) →
        CompHt.growthOn Y.U (q k) (AllWt.wtOf (T.Q.Dw j) la 0) = ENNReal.ofReal
          (GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
            (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) * (CompHt.vdm la : ℤ)) := by
  obtain ⟨q, hq, h⟩ := topSelf_eq_covol hP.p16 TF hc hY.geo (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ (hY.unf σ hσ)
  refine ⟨q, hq, fun k la hla => ?_⟩
  obtain ⟨_, hd, h⟩ := h k
  refine (growthOn_eq_topSelf hP hN hL hY hf _ TF hd hla).trans ?_
  rw [h, GlobalTheory.FlagPoly.flagDegFormula, CompHt.weylProd_eq,
    show ((CompHt.vdm la : ℤ) : ℝ) = _ from CompHt.map_vdm (Int.castRingHom ℝ) la]
  congr 1
  simp only [CompHt.dimFlag, eq_intCast]
  change GlobalTheory.TrueCx.covol ((Y.U σ).X k) * _ = _
  ring

theorem vZero_eq_covol (hP : Hypotheses₂) (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    Proport Y.U ∧ ∃ q : (Y.U σ).Comp ≃ Comp Y.d.Xo₂ Y.d.c₂,
      (∀ k (x : ((Y.U σ).X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF ((Y.U σ).un k x) s ∈ (q k).1) ∧
      ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
        (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := by
  obtain ⟨q, hq, h⟩ := growthOn_eq_covol hP hN hL hY hf TF hc hσ
  have hs : (0 : ℝ) < (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) :=
    Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt)
  have hv : ∀ k, CompHt.vZero Y.U (q k) = GlobalTheory.TrueCx.covol ((Y.U σ).X k) * (CompHt.dimFlag (T.Q.Dw j)).factorial /
      (CompHt.vdm (CompHt.stdWt (AllWt.Psi T.Q.H) ((T.Q.Dw j).p + (T.Q.Dw j).q)) : ℤ) := fun k => by
    have := GlobalTheory.TrueCx.covol_pos ((Y.U σ).X k)
    rw [CompHt.vZero, h k _ CompHt.strictAnti_stdWt, ENNReal.toReal_ofReal (by positivity), mul_div_cancel_right₀ _ hs.ne']
  refine ⟨fun Z la hla => ?_, q, hq, hv⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [h k la hla, CompHt.topDeg, hv]

theorem proport_of_charts (hP : Hypotheses₂) (hN : GlobalTheory.Published.NefNumerics)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (hc : ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x) : Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  obtain ⟨h, q, -, hv⟩ := vZero_eq_covol hP hN hL hY hf TF hc (σ := Y.d.c₂.F.val.toRingHom) rfl
  refine ⟨h, fun Z => ?_⟩
  obtain ⟨k, rfl⟩ := q.surjective Z
  rw [hv]
  exact div_pos (mul_pos (GlobalTheory.TrueCx.covol_pos _) (by positivity)) (Int.cast_pos.2 (CompHt.vdm_pos CompHt.strictAnti_stdWt))

theorem exists_torFlag_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
    (hs : SmoothOfRelativeDimension Dw.dim Y.s) (hb : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y))
    (hk : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y)) (hc : ∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChart Y x) :
    ∃ TF : TorFlag Xo c, ∀ x ∈ genBd TF.Y, HasToricChart TF.Y x :=
  ⟨⟨Y, hs, hb, hk, (GlobalTheory.FlagMod.FieldFlag.nonempty_flagModel E H Dw l Xo c Y hs (TorFlagEx.pushInvertible_of_hasTheta Y
    (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw hr l Xo c Y hs))).some⟩,
    fun x hx => (GlobalTheory.MumfordChart.hasChart_iff Y x).1 (hc x hx)⟩

end Good

end GlobalTheory.CompProport
