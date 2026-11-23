import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartSectionBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelClosedSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusCyclotomicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisLatticePresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPAdicNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointTangentFrameComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveModuleRankGenericSpreadStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliTangentFrameBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleGluingCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFifthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelSmoothFlagHeightStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem charZero_sec {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {d : ℕ} (h : IsArithVar q d)
    (U : X.Opens) [Nonempty U] : CharZero Γ(X, U) := by
  have := h.isIntegral
  have h0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
  exact (resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X (homOfLE le_top)) |>.1 h0

theorem exists_bundle {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type}
    [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z}
    {d : ℕ} (hq : IsArithVar q d) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (hpb : IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F))) (r : ℕ) (τ : E →+* ℂ)
    (kind : ℕ → Bool) (dual : Bool)
    (h : ∀ x : X, ∃ (U : X.Opens) (u : LocAssign Z r jB U), x ∈ U ∧ IsAffineOpen U ∧ IsLocFrame Z e jB πB r τ U u ∧
      IsLocLat Z e jB πB r τ kind U u) :
    ∃ (M : X.Modules) (uu : FrAssign Z M r jB), IsVB M r ∧ IsLieFrames Z e jB πB M r τ dual uu ∧
      IsLieLat Z e jB πB M r τ kind (fun _ => True) uu := by
  choose U u hx hU hfr hlat using h
  have hcov : ∀ x : X, ∃ i, x ∈ U i := fun x => ⟨x, hx x⟩
  have haff : IsAffineHom jB := MorphismProperty.of_isPullback hpb.flip (isAffineHom_of_isAffine _)
  have hsep : X.IsSeparated := by
    have : IsProper q := projProper _ _ _ hq.isProjOver
    exact ⟨by rw [← Limits.terminal.comp_from q]; infer_instance⟩
  have hc := GlobalTheory.T.integrality_criterion_normal_model F X W q _ jB d hq hn hpb
  choose A hA using fun i j => GlobalTheory.T.arithmetic_model_flag_height_first E H Dw l Xo c Oz β Z F e X W jB πB haff hc r τ kind (U i) (U j) (u i) (u j)
    ((hU i).inf (hU j)) (hfr i) (hfr j) (hlat i) (hlat j)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.arithmetic_model_flag_height_second E H Dw l Xo c Oz β Z F e X W q jB πB d hq hpb r τ X U u A hfr hA
  obtain ⟨M, f, hf, hm⟩ : ∃ (M : X.Modules) (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)),
      ∀ i j, FramesMatch Z jB πB dual (hf i) (f j) (u i) (u j) := by
    cases dual with
    | false =>
      obtain ⟨M, f, hf, hm⟩ := GlobalTheory.T.vector_bundle_gluing_cocycle X r X U A hcov h1 h2
      refine ⟨M, f, hf, fun i j K _ x h₁ h₂ h₃ a => ?_⟩
      simp only [cond_false, hm]
      exact hA i j K x h₁ h₂ h₃ a
    | true =>
      have hres : ∀ (U₁ U₂ U₃ : X.Opens) (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (s : Γ(X, U₁)),
          resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := fun U₁ U₂ U₃ h₁ h₂ s => by
        have := X.presheaf.map_comp (homOfLE h₁).op (homOfLE h₂).op
        exact (congrArg (fun φ => φ.hom s) this).symm
      obtain ⟨M, f, hf, hm⟩ := GlobalTheory.T.vector_bundle_gluing_cocycle X r X U
        (fun i j => ((A j i).map (resG X (inf_comm (U i) (U j)).le)).transpose) hcov
        (fun i => by rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one])
        (fun i j k V hij hjk hik => by
          have := congrArg Matrix.transpose
            (h2 k j i V (hjk.trans (inf_comm _ _).le) (hij.trans (inf_comm _ _).le) (hik.trans (inf_comm _ _).le))
          rw [Matrix.transpose_mul] at this
          convert this using 1
          · congr 1 <;> ext a b <;> exact hres _ _ _ _ _ _
          · ext a b
            exact hres _ _ _ _ _ _)
      refine ⟨M, f, hf, fun i j K _ x h₁ h₂ h₃ a => ?_⟩
      simp only [cond_true, hm, Matrix.transpose_apply, Matrix.map_apply]
      have h₄ : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U j ⊓ U i) := inf_comm (U i) (U j) ▸ h₃
      simp only [TangentOrigin.evalPt_res (x ≫ jB) _ h₄ h₃]
      exact hA j i K x h₂ h₁ h₄ a
  obtain ⟨uu, huu, hag⟩ := GlobalTheory.T.arithmetic_model_flag_height_third E H Dw l Xo c Oz β Z F e X W jB πB M r τ dual X U f hf u hcov hfr hm
  refine ⟨M, uu, fun x => ⟨U x, f x, hx x, hf x⟩, huu,
    GlobalTheory.T.arithmetic_model_flag_height_fourth E H Dw l Xo c Oz β Z F e X W jB πB M r τ dual kind X U f hf uu hcov huu fun i => ?_⟩
  rw [hag]
  exact hlat i

variable (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))

theorem exists_chart [IsGalois ℚ E] {X : Scheme.{0}} [IsIntegral X] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (h0 : ∀ (U : X.Opens) [Nonempty U], CharZero Γ(X, U)) (ρ : X ⟶ Z.X) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hd : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr E).natAbs → p ∈ S)
    (hζ : ∃ ζ : X.functionField, IsPrimitiveRoot ζ (∏ p ∈ S, p))
    (hs : GlobalTheory.HtGen.SplitK Z.t (K := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ ρ) (∏ p ∈ S, p)) (x : X) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∀ τ : E →+* ℂ, ∃ (n m : ℕ) (A : Fin m → Γ(X, V.1)), n ≠ 0 ∧
      (n : Γ(X, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧
      ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X, V.1) →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
        RingBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ρ) τ (Dw.mult τ) (ArIn.ind S) (scOf H τ (ArIn.ind S)) := by
  obtain ⟨V, g, e, hx, he⟩ := GlobalTheory.LineNorm.exists_affine_isTanBasis E H Z.X Z.t X ρ x
  refine ⟨V, hx, fun τ => ?_⟩
  have : Nonempty V.1 := ⟨⟨x, hx⟩⟩
  have := h0 V.1
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have hsep : Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  have : IsFractionRing Γ(X, V.1) X.functionField := functionField_isFractionRing_of_isAffineOpen X V.1 V.2
  have : CharZero X.functionField := charZero_of_injective_algebraMap (IsFractionRing.injective Γ(X, V.1) _)
  have : IsIntegrallyClosed Γ(X, V.1) :=
    haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hn x).1, fun x => (hn x).2⟩
    GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen V.2
  have hgen : spMap (algebraMap Γ(X, V.1) X.functionField) ≫ V.2.fromSpec ≫ ρ =
      X.fromSpecStalk (genericPoint X) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact V.2.fromSpecStalk_eq_fromSpecStalk (((genericPoint_spec X).mem_open_set_iff V.1.isOpen).2 ⟨x, trivial, hx⟩)
  obtain ⟨M, h, hP⟩ := GlobalTheory.T.split_torus_cyclotomic_point E H Z.X Z.t hsep S hS Γ(X, V.1) X.functionField (V.2.fromSpec ≫ ρ) hζ (hgen ▸ hs) g e he
  obtain ⟨M', h', hP'⟩ : ∃ (M' : ℕ) (h' : Fin M' → Fin g → Γ(X, V.1)),
      LatPres Z.t (R := Γ(X, V.1)) (V.2.fromSpec ≫ ρ) (ArIn.ind S) (scOf H τ (ArIn.ind S)) e h' := by
    by_cases hτ : τ (H.rt : E) = H.rt0
    · obtain ⟨m, d, ⟨n, hn0, hn⟩, hd'⟩ := GlobalTheory.T.different_ideal_p_adic_norm E inferInstance
      let κ : 𝓞 c.F →+* Γ(X, V.1) := (Spec.preimage (V.2.fromSpec ≫ ρ ≫ Z.s)).hom
      let i : 𝓞 E →+* Γ(X, V.1) := κ.comp (RingOfIntegers.mapRingHom (embF c τ))
      refine GlobalTheory.T.tangent_basis_lattice_presentation E H Z.X Z.t _ _ _ _ g M e h he hP m (fun k => i (d k)) ⟨n, hn0, ?_⟩ fun p _ φ => ?_
      · have := Ideal.mem_map_of_mem i hn
        rwa [map_natCast, Ideal.map_span, ← Set.range_comp] at this
      · refine (hd' p (φ.comp i)).trans ?_
        congr 2
        by_cases hp : p ∈ S
        · simp [scOf, ArIn.ind, hp, hτ]
        · have : ¬ p ∣ (NumberField.discr E).natAbs := fun h => hp (hd p Fact.out h)
          simp [scOf, ArIn.ind, hp, vDiff, padicValNat.eq_zero_of_not_dvd this]
    · refine ⟨M, h, ?_⟩
      have : scOf H τ (ArIn.ind S) = fun _ => 0 := funext fun p => by simp [scOf, hτ]
      rwa [this]
  obtain ⟨D, P, hD, hPr, hrk⟩ := GlobalTheory.T.moduli_point_tangent_frame_complex E H Dw l Xo c Z _ _ τ g e he
  obtain ⟨n, m, A, hn0, hA, hsp⟩ := GlobalTheory.T.projective_module_rank_generic_spread _ g M' (Dw.mult τ) D P h' hD hPr.1 hrk hP'.1
  refine ⟨n, m, A, hn0, hA, fun R' _ _ _ ψ hk => ?_⟩
  obtain ⟨N, U, I, hN, hU⟩ := hsp R' ψ hk
  exact GlobalTheory.T.moduli_tangent_frame_base_change E H Dw l Xo c _ _ Z _ R' ψ _ τ _ _ g M' _ D N e h' P U I hD hN he hPr hP' hU

theorem exists_base [IsGalois ℚ E] {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {V : Scheme.{0}} [IsIntegral V]
    (j : V ⟶ gen Z) (hj : IsClosedImmersion j) {d : ℕ} (hdim : topologicalKrullDim V = d) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hd : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr E).natAbs → p ∈ S) :
    ∃ (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X),
      IsPre (genStr Z ≫ spMap e.toRingHom) (Set.range j) d (genι Z) q jB πB ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ (τ : E →+* ℂ) (x : X),
        ∃ (U : X.Opens) (u : LocAssign Z (Dw.mult τ) jB U), x ∈ U ∧ IsAffineOpen U ∧
          IsLocFrame Z e jB πB _ τ U u ∧ IsLocLat Z e jB πB _ τ (ArIn.ind S) U u := by
  classical
  obtain ⟨X₀, W₀, q₀, j₀, π₀, ρ₀, h₀⟩ := GlobalTheory.T.arithmetic_model_closed_subvariety F c.F e Z.X Z.s Z.proj V j hj d hdim
  have := h₀.1.isIntegral
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CharZero X₀.functionField := by
    have := charZero_sec h₀.1 ⊤
    exact charZero_of_injective_ringHom (f := (X₀.germToFunctionField ⊤).hom) (X₀.germToFunctionField_injective ⊤)
  have hn0 : ∏ p ∈ S, p ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hS p hp).ne_zero
  let x₀ : Sp X₀.functionField ⟶ Z.X := X₀.fromSpecStalk (genericPoint X₀) ≫ ρ₀
  obtain ⟨K, i1, i2, i3, hfin, hinj, -, ⟨ζ, hζ⟩, hs⟩ :=
    GlobalTheory.T.exists_finite_extension_splitting_torsion E H Z.X Z.t X₀.functionField x₀ _ hn0
  have hK : IsField K := by
    have : Algebra.IsIntegral X₀.functionField K := Algebra.IsIntegral.of_finite _ _
    exact (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField _)
  letI : Field K := hK.toField
  obtain ⟨X₁, W₁, _, ν₁, j₁, π₁, κ, h₁, hn₁, hκ⟩ := GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₀ W₀ q₀ j₀ π₀ ρ₀ h₀ K hfin
  have hsK : GlobalTheory.HtGen.SplitK Z.t (K := X₁.functionField) (X₁.fromSpecStalk (genericPoint X₁) ≫ ν₁ ≫ ρ₀)
      (∏ p ∈ S, p) :=
    GlobalTheory.HtGen.SplitCover.splitK_of_splitTors Z.t _ κ _ (by rw [reassoc_of% hκ]) hs
  choose V hV hch using exists_chart Z hn₁ (fun U _ => charZero_sec h₁.1 U) (ν₁ ≫ ρ₀) S hS hd
    ⟨κ ζ, hζ.map_of_injective κ.injective⟩ hsK
  choose n m A hn hA hR using hch
  have : IsProper (ν₁ ≫ q₀) := projProper _ _ _ h₁.1.isProjOver
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (ν₁ ≫ q₀)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X₁ => ((V x).1 : Set X₁)) (fun x => (V x).1.isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hV x⟩
  let ε := (Fintype.equivFin (t × (E →+* ℂ))).symm
  obtain ⟨X₂, W₂, b, j₂, π₂, h₂, hb⟩ := GlobalTheory.T.arithmetic_model_affine_cover_radical F _ _ _ _ d _ X₁ W₁ _ j₁ π₁ _ h₁ _ (fun k => (V (ε k).1).1)
    (fun k => m (ε k).1 (ε k).2) (fun k => A (ε k).1 (ε k).2) (fun k => n (ε k).1 (ε k).2) (fun k => (V _).2)
    (fun k => hn _ _) (fun k => hA _ _)
  have := h₂.1.isIntegral
  obtain ⟨X₃, W₃, _, ν₃, j₃, π₃, -, h₃, hn₃, -⟩ :=
    GlobalTheory.T.arithmetic_model_finite_extension F _ _ _ _ d _ X₂ W₂ _ j₂ π₂ _ h₂ X₂.functionField inferInstance
  refine ⟨X₃, W₃, _, j₃, π₃, _, h₃, hn₃, fun τ w => ?_⟩
  obtain ⟨x, hx, hw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((ν₃ ≫ b) w)))
  obtain ⟨k, hk⟩ := ε.surjective (⟨x, hx⟩, τ)
  have hw' : (ν₃ ≫ b) w ∈ (V (ε k).1).1 := by rw [hk]; exact hw
  obtain ⟨U, hU, hwU, hUa, hdv⟩ := hb X₃ ν₃ w k hw'
  have : Nonempty U := ⟨⟨w, hwU⟩⟩
  have := charZero_sec h₃.1 U
  have hRB := hR (ε k).1 (ε k).2 Γ(X₃, U) _ hdv
  have e₁ : spMap ((ν₃ ≫ b).appLE (V (ε k).1).1 U hU).hom ≫ (V (ε k).1).2.fromSpec ≫ ν₁ ≫ ρ₀ =
      hUa.fromSpec ≫ ν₃ ≫ b ≫ ν₁ ≫ ρ₀ := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec (ν₃ ≫ b) (V (ε k).1).2 hUa hU
    rw [← Category.assoc]
    refine (congrArg (· ≫ ν₁ ≫ ρ₀) this).trans ?_
    simp only [Category.assoc]
  have hτ : (ε k).2 = τ := by rw [hk]
  rw [e₁, hτ] at hRB
  obtain ⟨u, hu⟩ := GlobalTheory.T.arithmetic_model_flag_compactification E H Dw l Xo c _ _ Z F e X₃ W₃ j₃ π₃ _ h₃.2.2.2.2 U hUa τ _ _ hRB
  exact ⟨U, u, hwU, hUa, hu⟩

end Free

theorem exists_comp {D : D7} (O : Setup D) (c : O.s.Comp) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (j : V ⟶ gen O.s.T.Z), IsClosedImmersion j ∧
      topologicalKrullDim V = (dimGr D.what₂.Tau O.N O.j : ℕ) ∧ Set.range j = Set.range (O.Φ.C c).π := by
  have hsm := O.s.T.smooth
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.CompOfVar.exists_var_comp _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e hsm (O.Φ.C c).Y
    (O.Φ.C c).π (O.Φ.C c).π_str
  let f : (O.Φ.C c).Y.X ⟶ X.X := IsOpenImmersion.lift j (O.Φ.C c).π hr
  have hf : f ≫ j = (O.Φ.C c).π := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range j = Set.range (O.Φ.C c).π := by
    refine Set.Subset.antisymm ?_ hr
    rintro _ ⟨z, rfl⟩
    obtain ⟨K, _, _, x, t, rfl⟩ := GlobalTheory.FlagCptBase.exists_geomPt _ z
    let χ : O.κ.c.F →+* K := (Spec.preimage (x ≫ j ≫ genStr O.s.T.Z)).hom
    have hχ : x ≫ j ≫ genStr O.s.T.Z = spMap χ := (Spec.map_preimage _).symm
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z K χ (x ≫ j) (by rw [Category.assoc, hχ])
    rw [Category.assoc] at g
    obtain ⟨p, ⟨hp, -⟩, -⟩ := GlobalTheory.CarryAll.carries_everywhere _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c X j hoi hj f hf
      K χ x hχ g
    refine ⟨p t, ?_⟩
    rw [← hf, ← hp]
    simp only [Scheme.Hom.comp_apply]
  refine ⟨X.X, inferInstance, j, IsClosedImmersion.of_isPreimmersion _
    (hrange ▸ GlobalTheory.FlagCptBase.isClosed_range_π (O.Φ.C c)), ?_, hrange⟩
  have h : SmoothOfRelativeDimension (0 + O.S.Dw.dim) (j ≫ genStr O.s.T.Z) := inferInstance
  rw [GlobalTheory.HSApp.BigMoving.dim_eq _ X.X _ _ h, zero_add, Datum.dim, dimGr, GlobalTheory.ShFam.CmDim.card_tau, O.S.p_eq,
    show O.S.Dw.q = O.N - O.j by have := O.S.rank_eq; have := O.S.p_eq; omega, mul_assoc]

theorem exists_lieBase : ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    ∃ (Bs : Scheme.{0}) (_ : IsIntegral Bs) (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (_ : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
      (_ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
      (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (_ : ∀ a, (h a).IsCInf), LieBase O B R c q E h := by
  intro D O ⟨x, P, hc⟩ B R hR c
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨V, _, j, hj, hdim, hr⟩ := exists_comp O c
  have hd0 : 2 * (NumberField.discr D.host.E).natAbs ≠ 0 :=
    mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
  obtain ⟨X, W, q, jB, πB, ρ, ⟨hq, hpb, hfin, hrg, -⟩, hn, hloc⟩ := exists_base O.s.T.Z O.κ.e j hj hdim
    (FlagAr.setB O.Y B)
    (fun p hp => by
      rw [O.setB_eq] at hp
      rcases Finset.mem_union.1 hp with h | h
      exacts [(Finset.mem_filter.1 h).2, Nat.prime_of_mem_primeFactors h])
    (fun p hp h => Finset.mem_union_right _ (Finset.mem_union_left _
      (Nat.mem_primeFactors.2 ⟨hp, h.mul_left 2, hd0⟩)))
  have hrk : ∀ a : D.what₂.Tau × Bool, rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a) := by
    rintro ⟨τ, _ | _⟩
    · have := O.S.rank_eq
      have := O.S.p_eq
      change O.N - O.j = O.S.Dw.mult (conjEmb (DV.tauEmb D τ))
      rw [GlobalTheory.Harm.mult_conjEmb_of_mem O.S.Dw (Amb.cm O.A τ)]
      omega
    · exact ((GlobalTheory.Harm.mult_of_mem O.S.Dw (Amb.cm O.A τ)).trans O.S.p_eq).symm
  choose E uu hvb hfr hlat using fun a : D.what₂.Tau × Bool =>
    exists_bundle O.s.T.Z O.κ.e hq hn hpb (rkB D.what₂.Tau O.N O.j a) (embB D a) (ArIn.ind (FlagAr.setB O.Y B)) (!a.2)
      (by rw [hrk]; exact hloc _)
  let G : ∀ σ', EigMet O.s.T.Z σ' := fun σ' => x.eigMetAt σ' (some R)
  have hG : EigConj O.s.T.Z G := fun σ σ' y y' g g' τ hσ e hg => GlobalTheory.ShFam.ConjMet.eigMetAt_conj x hσ e hg τ _
  choose h hh using fun a : D.what₂.Tau × Bool =>
    GlobalTheory.T.arithmetic_model_flag_height_fifth _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E a) _ _ _ (hrk a) (uu a) G (hvb a) (hfr a) hG
  have hsm := O.s.T.smooth
  refine ⟨X, hq.isIntegral, q, hq, hn, E, h, fun a => GlobalTheory.T.arithmetic_model_smooth_flag_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E a) _ _ _
    (hrk a) (uu a) G (h a) (hfr a) (fun σ' => ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ x σ' R hR
      (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x σ')) (hh a),
    W, jB, πB, hpb, uu, G, hfin, hrg.trans hr, hfr, hlat, fun σ n => ?_, fun a => ⟨hrk a, hh a⟩⟩
  rw [hc.hm_eq]
  rfl

end GlobalTheory.ArLieBase

end
