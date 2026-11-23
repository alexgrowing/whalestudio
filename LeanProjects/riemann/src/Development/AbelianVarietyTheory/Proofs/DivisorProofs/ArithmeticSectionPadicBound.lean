import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeCoordinateGradedNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationSectionWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointComplexTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsIntegralCombinationStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link.IntPtNorm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_ext (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ Z.X) :
    ∃ xV : Sp V ⟶ Z.X, spMap (algebraMap V K) ≫ xV = x := by
  have := isProper_toroidalModel_structureMap Z
  let φ : 𝓞 c.F →+* K := (Spec.preimage (x ≫ Z.s)).hom
  have hφ : ∀ a, φ a ∈ (algebraMap V K).range := fun a => by
    have h1 : IsIntegral V (φ a) := (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) φ
      (RingHom.ext_int _ _)
    exact (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K)).1 h1
  let eV : V ≃+* (algebraMap V K).range := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let φV : 𝓞 c.F →+* V := eV.symm.toRingHom.comp (φ.codRestrict _ hφ)
  have hc : (algebraMap V K).comp φV = φ := RingHom.ext fun a =>
    congrArg Subtype.val (eV.apply_symm_apply (φ.codRestrict _ hφ a))
  have hv : ValuativeCriterion.Existence Z.s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s)
    exact h.1
  let S : ValuativeCommSq Z.s :=
    { R := V, K := K, i₁ := x, i₂ := spMap φV
      commSq := ⟨by
        rw [← Spec.map_preimage (x ≫ Z.s)]
        exact ((OpenReg.spMap_comp (algebraMap V K) φV).trans (congrArg spMap hc)).symm⟩ }
  obtain ⟨⟨xO, h1, -⟩⟩ := (hv S).exists_lift
  exact ⟨xO, h1⟩

theorem ptF_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : AllWt.ptF z = spMap φ.toRingHom ≫ AllWt.ptF y := by
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ptF_fst, ptF_fst, h.1]
  · rw [Category.assoc, ptF_snd, ptF_snd, OpenReg.spMap_comp]
    exact congrArg spMap φ.comp_algebraMap.symm

theorem grNorm_eq_one (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (jm : T.Fr →+* C)
    (hψ : ∀ z : T.V, ‖jm (algebraMap T.V T.Fr z)‖ ≤ 1) :
    letI := io.toAlgebra; letI := (jm.comp io).toAlgebra
    ∀ (yC : FrPt Xo c C), FrMap (⟨jm, fun _ => rfl⟩ : T.Fr →ₐ[c.F] C) y.1 yC →
      ∀ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ Z.t.G.left),
      (∀ τ i, ∃ w : Sp (DualNumber C) ⟶ Z.oF.t.G.left,
        w ≫ Z.oF.t.G.hom = spMap (algebraMap C (DualNumber C)) ≫ AllWt.ptF yC ∧ w ≫ Z.m0.toSABMap.φ = yC.u τ i ∧
          w ≫ Z.m.φ = u τ i) → ∀ τ i,
      grNorm Z.t ((AllWt.ptF yC ≫ Z.jQ) ≫ genι Z) (latDR Z.t ((AllWt.ptF yC ≫ Z.jQ) ≫ genι Z)) (u τ) i = 1 := by
  letI := io.toAlgebra
  letI := (jm.comp io).toAlgebra
  intro yC hmap u hu τ i
  have hpt : AllWt.ptF yC = spMap jm ≫ AllWt.ptF y.1 := (ptF_of_frMap hmap :)
  obtain ⟨xV, hxV⟩ := exists_ext Z T.V T.Fr (AllWt.ptF y.1 ≫ Z.jQ ≫ genι Z)
  obtain ⟨v, hv, hw, hsat⟩ := GlobalTheory.T.integral_point_complex_tangent_vector _ _ _ _ _ _ _ _ Z T io y xV hxV τ
  have hx : (AllWt.ptF yC ≫ Z.jQ) ≫ genι Z = spMap (jm.comp (algebraMap T.V T.Fr)) ≫ xV := by
    rw [← OpenReg.spMap_comp, Category.assoc, Category.assoc, hxV, hpt, Category.assoc]
  have hvec : u τ = fun a => spMap (dualMap (jm.comp (algebraMap T.V T.Fr))) ≫ v a := funext fun a => by
    obtain ⟨w, w1, w2, w3⟩ := hw a
    obtain ⟨w', w1', w2', w3'⟩ := hu τ a
    have : w' = spMap (dualMap jm) ≫ w := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [w2', Category.assoc, w2]
        exact hmap.2.1 τ a
      · rw [w1', Category.assoc, w1, hpt, ← Category.assoc, ← Category.assoc, OpenReg.spMap_comp, OpenReg.spMap_comp,
          GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]
    rw [← GlobalTheory.GradedPieces.dual_comp, ← w3, ← Category.assoc, ← this]
    exact w3'.symm
  rw [hvec, hx]
  exact GlobalTheory.T.tangent_vectors_integral_combination _ _ _ Z.t T.V T.Fr xV _ v hv hsat C _ hψ (Guard.existsUnique_ext Z _) i

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem comp_eq (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c) (hk : Over Φ k Z) {K : Type} [Field K] [Algebra κ.c.F K]
    (y : FrPt s.Xo κ.c K) (hy : AllWt.LiesOn Z y) (i : s.Comp) (q : Sp K ⟶ (Φ.C i).Y.X)
    (h : q ≫ (Φ.C i).π = AllWt.ptF y ≫ s.T.Z.jQ) : i = k := by
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  have uniq : ∀ (a : s.Comp) {Z Z' : Comp s.Xo κ.c}, Over Φ a Z → Over Φ a Z' → Z = Z' := fun a Z Z' h h' => by
    by_contra hne
    let u : Sp (Φ.C a).Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Φ.C a).Y.Fn)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) (h u) (h' u)
  let t : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have ht : (Φ.C i).π (q t) = s.T.Z.jQ (AllWt.ptF y t) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  have hW := GlobalTheory.ShFam.PtComp.preimage_connectedComponent_mem s.T.Z hsm ((Φ.C i).π (q t))
  have eZ : (⟨_, hW⟩ : Comp s.Xo κ.c) = Z := by
    by_contra hne
    refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) ?_ (hy t)
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [ht]
    exact mem_connectedComponent
  have hO' : Over Φ i Z := by
    intro u
    rw [← eZ]
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [← Scheme.Hom.comp_apply _ s.T.Z.jQ, (Φ.C i).y0_x, Scheme.Hom.comp_apply]
    exact (isPreconnected_range (Φ.C i).π.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := GlobalTheory.CovHt.Link.exists_equiv_over D A N j S κ s Φ
  refine r.injective ?_
  rw [uniq i (hr i) hO', uniq k (hr k) hk]

theorem vV_nonneg (T : CDVR) (z : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr z) := by
  by_cases hz : algebraMap T.V T.Fr z = 0
  · simp [hz, vV]
  · have h1 : valV T.V (algebraMap T.V T.Fr z) ≤ 1 := HeightOneSpectrum.valuation_le_one _ z
    have := (WithZero.log_le_log (valV_ne_zero hz) one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    simp only [vV]
    omega

end GlobalTheory.CovHt.Link.IntPtNorm

open GlobalTheory.CovHt.Link.IntPtNorm in

theorem GlobalTheory.CovHt.Link.exists_pt_drAt_eq : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw) (g : Rul s.Xo κ.c), g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) → (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (pl : HeightOneSpectrum (𝓞 κ.c.F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 κ.c.F) ∈ pl.asIdeal → ∀ (T : CDVR) (io : κ.c.F →+* T.Fr) (e : ℕ), OverLa pl T.V io e → ∀ y : IntFr s.Xo κ.c T io, T.FinRes → (letI := io.toAlgebra; AllWt.LiesOn Z y.1) → ∀ jm : T.Fr →+* ℂ_[p], (∀ z : T.Fr, z ≠ 0 → ‖jm z‖ = (p : ℝ) ^ (-((vV T.V z : ℝ) / (vV T.V (io (p : κ.c.F)) : ℝ)))) → ∃ x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X, drAt Φ k la p x ((Φ.C k).val g) = ‖jm (evI y g)‖ := by
  intro _ _ D A N j S κ s Φ k Z hOv la g hg _ pl p hpp _ T io e _ y _ hly jm hjm
  letI := io.toAlgebra
  letI := (jm.comp io).toAlgebra
  let jm' : T.Fr →ₐ[κ.c.F] ℂ_[p] := ⟨jm, fun _ => rfl⟩
  obtain ⟨yC, hmap⟩ := GlobalTheory.FlagTan.exists_frMap jm' y.1
  have hev : evR s.Xo κ.c g yC = jm (evI y g) := GlobalTheory.FlagTan.evR_frMap hg.1 hmap
  have hpt : AllWt.ptF yC = spMap jm ≫ AllWt.ptF y.1 := (ptF_of_frMap hmap :)
  have hlies : AllWt.LiesOn Z yC := fun u => by
    rw [hpt, Scheme.Hom.comp_apply]
    exact hly _
  have hstr : (AllWt.ptF yC ≫ s.T.Z.jQ) ≫ genStr s.T.Z = spMap (algebraMap κ.c.F ℂ_[p]) :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) s.T.Z.jQ_over).trans (ptF_snd yC))
  obtain ⟨gf, hmatch⟩ : ∃ gf : EigFrame s.T.Z (algebraMap κ.c.F ℂ_[p]) ((AllWt.ptF yC ≫ s.T.Z.jQ) ≫ genι s.T.Z),
      ∀ τ i, ∃ w : Sp (DualNumber ℂ_[p]) ⟶ s.T.Z.oF.t.G.left,
        w ≫ s.T.Z.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ AllWt.ptF yC ∧
          w ≫ s.T.Z.m0.toSABMap.φ = yC.u τ i ∧ w ≫ s.T.Z.m.φ = gf.v τ i :=
    ⟨EigFrame.ofFrPt s.T.Z yC (Category.assoc _ _ _).symm, fun τ i =>
      (EigFrame.ofFrPt_v s.T.Z yC (Category.assoc _ _ _).symm τ i).imp fun w h => ⟨h.1.1, h.2⟩⟩
  have hgr : ∀ τ i, grNorm s.T.Z.t ((AllWt.ptF yC ≫ s.T.Z.jQ) ≫ genι s.T.Z)
      (latDR s.T.Z.t ((AllWt.ptF yC ≫ s.T.Z.jQ) ≫ genι s.T.Z)) (gf.v τ) i = 1 := by
    refine grNorm_eq_one s.T.Z T io y jm (fun z => ?_) yC hmap gf.v hmatch
    by_cases hz : algebraMap T.V T.Fr z = 0
    · simp [hz]
    · rw [hjm _ hz]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.out.one_le) (neg_nonpos.2 (div_nonneg ?_ ?_))
      · exact_mod_cast vV_nonneg T z
      · have := vV_nonneg T (p : T.V)
        rw [map_natCast] at this ⊢
        exact_mod_cast this
  haveI := PadicComplex.isAlgClosed p
  obtain ⟨⟨i, q⟩, ⟨hq, hcar⟩, -⟩ := Φ.lifts ℂ_[p] (algebraMap κ.c.F ℂ_[p]) (AllWt.ptF yC ≫ s.T.Z.jQ) hstr gf
  obtain rfl := comp_eq Φ k Z hOv yC hlies i q hq
  have hco := GlobalTheory.T.flag_compactification_section_weight _ _ _ _ _ _ _ _ s.T.Z _ _ (Φ.C i) (exOf S.Dw la 0) g rfl hg ℂ_[p] yC _ gf hmatch q hq hcar
  rw [← expo_drSym] at hco
  exact ⟨q, (GlobalTheory.T.eigenframe_coordinate_graded_norm D A N j S κ s Φ i la ℂ_[p] p q _ _ _ gf _ hgr hco).trans (congrArg _ hev)⟩
