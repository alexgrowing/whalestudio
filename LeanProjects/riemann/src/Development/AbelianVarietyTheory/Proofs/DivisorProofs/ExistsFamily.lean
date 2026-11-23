import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpectralResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterOfSpectralResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalSplitTorusBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalTorusSectionsBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusExtendsNormalLocalStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EqFamily

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X],
    1 ≤ Dw.p + Dw.q → ∀ (S : Scheme.{0}) [IsIntegral S] (ρ : S ⟶ Z.X) (p : ℕ) [Fact p.Prime] (n : ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → CharZero S.functionField → (∃ ζ : S.functionField, IsPrimitiveRoot ζ (p ^ n)) →
    SplitK Z.t (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) → ρ (genericPoint S) ∈ Set.range Z.j →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) ℤ Dw.La),
    ∃ ch : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (y ≫ ρ) (p ^ n),
      (∀ y, Gens fun m => ch m y) ∧ (∀ y, GlobalTheory.EqHalf.Equivar Z.t (fun m => ch m y) (GlobalTheory.EqHalf.chiAct Dw b)) ∧
      (∀ (U : S.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ Z.t.G.left)),
        IsTanBasis Z.t (R := Γ(S, U)) (hU.fromSpec ≫ ρ) e → ∃ h : Fin N → Fin g → Γ(S, U),
          ∀ (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S), spMap x ≫ hU.fromSpec = y →
            ∀ j, DlogIs Z.t p n (ch j y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) ∧
      ∀ (y : Sp ↥(intO ℂ_[p]) ⟶ S) (K : Type) [Field K] (k : K →+* ℂ_[p]) (z₀ : Sp K ⟶ Xo.XF c),
        (∀ a : K, IsAlgebraic ℤ a) → spMap (intO ℂ_[p]).subtype ≫ y ≫ ρ = spMap k ≫ z₀ ≫ Z.j →
        ∃ (yy : Sp ℂ_[p] ⟶ Xo.XF c) (s : Fin N → (Over.mk yy ⟶ Z.oF.t.G)) (ζ : ℂ_[p]ˣ), IsPrimitiveRoot ζ (p ^ n) ∧
          HasPoint Z.oF.t Z.m.φ (y ≫ ρ) yy ∧ IsGram Z.oF.t (p ^ n) s ζ (GlobalTheory.EqHalf.gram Dw b) ∧
          ∀ m, IsWeilChar Z.oF.t Z.m.φ (s m) (ch m y) := by
  intro E _ _ _ H Dw l Xo c Z _ hpq S _ ρ p _ n hN hK hζ hsplit hgp N bs
  have hHom : HomSt := GlobalTheory.T.homomorphism_result
  have hExt : ExtSt := GlobalTheory.T.extension_result
  have hSpec : SpecSt := GlobalTheory.T.spectral_result
  have hChar : CharSt := GlobalTheory.T.character_of_spectral_result GlobalTheory.T.spectral_result
  have hGens : GensSt := GlobalTheory.T.generators_result
  have hLift : LiftSt := GlobalTheory.T.lifting_result
  have hPt : PointSt := GlobalTheory.T.point_result_of_integrality GlobalTheory.T.integrality_result
  classical
  haveI : CharZero S.functionField := hK
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  haveI := GlobalTheory.DetHT.mono_j_int Z
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) =
      S.fromSpecStalk (genericPoint S) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)
  obtain ⟨ξ₀, hξ₀⟩ := GlobalTheory.DetHT.exists_lift_int Z (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (by
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum S.functionField) _ _
    exact ((Scheme.Hom.comp_apply _ _ _).trans (congrArg ρ Scheme.fromSpecStalk_closedPoint)).symm ▸ hgp)
  obtain ⟨s, ζ, hζp, hG, hsg, hact⟩ := GlobalTheory.T.toroidal_split_torus_basis E H Dw l Xo c _ _ Z S.functionField ξ₀ (p ^ n) hq hζ (hξ₀ ▸ hsplit) N bs
  obtain ⟨χ, hχ, hχg⟩ := hHom E H Dw l Xo c _ _ Z S.functionField ξ₀ _ hξ₀ (p ^ n) hq N s ζ _ hζp (GlobalTheory.EqHalf.isUnit_det_gram Dw bs) hG hsg
  have key (s : S) := by
    haveI := (hN s).1
    haveI := (hN s).2
    exact GlobalTheory.T.integral_point_extension_split E H Z.X Z.t S.functionField _ (p ^ n) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)
  have hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) :
      spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)
  have L (y : Sp ↥(intO ℂ_[p]) ⟶ S) := (key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ)
    inferInstance (hz y)
  let ch : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (y ≫ ρ) (p ^ n) :=
    fun j y => Classical.choose ((L y).1 (χ j))
  have hc (j : Fin N) (y : Sp ↥(intO ℂ_[p]) ⟶ S) := Classical.choose_spec ((L y).1 (χ j))
  have memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S)
      (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]
    exact ⟨_, rfl⟩
  refine ⟨ch, fun y => ?_, fun y => ?_, fun U hU g e he => ?_,
    fun y K _ k z₀ hK hy => ?_⟩
  · haveI := (hN (y (IsLocalRing.closedPoint _))).1
    haveI := (hN (y (IsLocalRing.closedPoint _))).2
    exact hGens E H Z.X Z.t S.functionField _ (p ^ n) hq hζ hsplit _ _ (hgen _) p _ _ inferInstance (hz y) N χ _ hχg
      fun m => hc m y
  · haveI := (hN (y (IsLocalRing.closedPoint _))).1
    haveI := (hN (y (IsLocalRing.closedPoint _))).2
    exact GlobalTheory.T.split_torus_extends_normal_local E H Z.X Z.t S.functionField _ (p ^ n) hq hζ hsplit _ _ (hgen _) p _ _ inferInstance (hz y) N χ _ _
      (GlobalTheory.T.toroidal_torus_sections_basis E H Dw l Xo c _ _ Z S.functionField ξ₀ _ hξ₀ (p ^ n) hq N bs s ζ hG hsg hact χ hχ) fun m => hc m y
  · by_cases hne : Nonempty U
    swap
    · exact ⟨fun _ _ => 0, fun x y hxy _ => absurd ⟨⟨_, memU U hU x y hxy⟩⟩ hne⟩
    haveI : IsIntegrallyClosed Γ(S, U) := GlobalTheory.LineNorm.Chart.isIntegrallyClosed_sections hN hU
    haveI := functionField_isFractionRing_of_isAffineOpen S U hU
    have hgU : genericPoint S ∈ U := by
      obtain ⟨u⟩ := hne
      exact (genericPoint_specializes u.1).mem_open U.isOpen u.2
    have hchart : spMap (algebraMap Γ(S, U) S.functionField) ≫ (hU.fromSpec ≫ ρ) = S.fromSpecStalk (genericPoint S) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hgU]
      rfl
    choose hh hhs using fun j : Fin N =>
      GlobalTheory.T.integral_point_torsion_split E H Z.X Z.t S.functionField _ p n hsplit Γ(S, U) (hU.fromSpec ≫ ρ) hchart g e he.1 (χ j)
    refine ⟨hh, fun x y hxy j => ?_⟩
    have hs := memU U hU x y hxy
    let φ := (S.presheaf.germ U _ hs).hom
    have hu : (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField).comp φ =
        algebraMap Γ(S, U) S.functionField := by
      show (S.presheaf.germ U _ hs ≫ S.presheaf.stalkSpecializes (genericPoint_specializes _)).hom = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    have hx0 : spMap φ ≫ hU.fromSpec ≫ ρ = S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hs]
      rfl
    have heq : (Scheme.stalkClosedPointTo y).hom.comp φ = x := by
      apply GlobalTheory.LineNorm.Chart.ringHom_ext hU
      rw [hxy]
      show Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ hU.fromSpec = y
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      show _ ≫ hU.fromSpecStalk hs = y
      rw [hU.fromSpecStalk_eq_fromSpecStalk hs]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
    have k : DlogIs Z.t p n (ch j y) (fun i => spMap (dualMap ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ e i)
        (fun i => ((Scheme.stalkClosedPointTo y).hom.comp φ) (hh j i)) :=
      hhs j _ φ _ _ _ _ (ch j y) hu hx0 inferInstance (hz y) (hc j y)
    rw [heq] at k
    exact k
  · obtain ⟨ω, hω⟩ : ∃ ω : Sp ℂ_[p] ⟶ S, ω = spMap (intO ℂ_[p]).subtype ≫ y := ⟨_, rfl⟩
    let a : S := y (IsLocalRing.closedPoint _)
    let b : S := ω (IsLocalRing.closedPoint _)
    have hba : b ⤳ a := by
      have : b = y (spMap (intO ℂ_[p]).subtype (IsLocalRing.closedPoint _)) := by simp only [b, hω]; rfl
      rw [this]
      exact (IsLocalRing.specializes_closedPoint _).map y.continuous
    haveI := (hN a).1
    haveI := (hN a).2
    haveI := (hN b).1
    haveI := (hN b).2
    let r : S.presheaf.stalk a →+* S.presheaf.stalk b := (S.presheaf.stalkSpecializes hba).hom
    let ψ' : S.presheaf.stalk b →+* ℂ_[p] := (Scheme.stalkClosedPointTo ω).hom
    have hψ' : spMap ψ' ≫ S.fromSpecStalk b = ω := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ω
    have hr : spMap r ≫ S.fromSpecStalk a = S.fromSpecStalk b := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hba
    have hωρ : spMap ψ' ≫ S.fromSpecStalk b ≫ ρ = (spMap k ≫ z₀) ≫ Z.j := by
      rw [← Category.assoc, hψ', hω, Category.assoc, hy, Category.assoc]
    obtain ⟨x₀, hx₀⟩ := hLift E H Dw l Xo c Z _ _ ψ' inferInstance (S.fromSpecStalk b ≫ ρ) _ hωρ
    have h1 : spMap (algebraMap (S.presheaf.stalk b) S.functionField) ≫ x₀ = ξ₀ := by
      rw [← cancel_mono Z.j, Category.assoc, hx₀, hgen, hξ₀]
    have h2 : spMap ψ' ≫ x₀ = spMap k ≫ z₀ := by rw [← cancel_mono Z.j, Category.assoc, hx₀, hωρ]
    have h3 : ψ'.comp r = (intO ℂ_[p]).subtype.comp (Scheme.stalkClosedPointTo y).hom := by
      have e : spMap (ψ'.comp r) ≫ S.fromSpecStalk a =
          spMap ((intO ℂ_[p]).subtype.comp (Scheme.stalkClosedPointTo y).hom) ≫ S.fromSpecStalk a := by
        rw [spMap_comp_eq, spMap_comp_eq, Category.assoc, Category.assoc, hr, hψ', hω]
        exact congrArg (_ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e))
    have h4 : (algebraMap (S.presheaf.stalk b) S.functionField).comp r = algebraMap (S.presheaf.stalk a) S.functionField :=
      congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkSpecializes_comp S.presheaf _ _)
    have hinj := IsFractionRing.injective (S.presheaf.stalk b) S.functionField
    choose s' hs' hs'' using fun m => hExt E H Dw l Xo c _ _ Z _ _ x₀ ξ₀ h1 (p ^ n) hq (s m) (hG.1 m)
    let o : Over.mk (spMap k ≫ z₀) ⟶ Over.mk x₀ := Over.homMk (spMap ψ') h2
    obtain ⟨ζ₀, hζ₀⟩ := GlobalTheory.HtChar.root_mem (R := S.presheaf.stalk b) hq
      (u := (ζ : S.functionField)) (by rw [← Units.val_pow_eq_pow_val, hζp.pow_eq_one, Units.val_one])
    have hp₀ : IsPrimitiveRoot ζ₀ (p ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap _ S.functionField)
        (by rw [hζ₀]; exact IsPrimitiveRoot.coe_units_iff.2 hζp) hinj
    let ζ' := (hp₀.isUnit hq).unit
    have hζ' : Units.map (algebraMap (S.presheaf.stalk b) S.functionField).toMonoidHom ζ' = ζ := Units.ext hζ₀
    refine ⟨spMap k ≫ z₀, fun m => o ≫ s' m, Units.map ψ'.toMonoidHom ζ',
      IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.HtChar.prim_map ψ' hq hp₀), hPt E H Dw l Xo c Z hpq p K k z₀ hK _ _ rfl (by
      rw [hy, Category.assoc]), ⟨fun m => ?_, fun m m' => ?_⟩, fun m => ?_⟩
    · rw [← MonObj.comp_pow, hs', MonObj.comp_one]
    · rw [← map_zpow]
      refine hSpec E H Dw l Xo c _ _ Z _ _ _ _ ψ' hinj x₀ ξ₀ _ (p ^ n) hq (s' m) (s' m') (s m) (s m') _ _ (hs' m) (hs' m')
        (hs'' m).symm (hs'' m').symm rfl rfl _ ?_
      rw [map_zpow, hζ']
      exact hG.2 m m'
    · exact hChar E H Dw l Xo c _ _ Z S.functionField ξ₀ _ hξ₀ (p ^ n) hq hζ hsplit _ _ (hgen a) _ r _ x₀ hinj h4
        (by rw [hx₀, ← Category.assoc, hr]) h1 p _ ψ' _ _ inferInstance h3 (hz y) h2 (s m) (s' m) _ (hs' m) (hs'' m).symm rfl
        (χ m) _ (hχ m) (hc m y)

end GlobalTheory.EqFamily

end
