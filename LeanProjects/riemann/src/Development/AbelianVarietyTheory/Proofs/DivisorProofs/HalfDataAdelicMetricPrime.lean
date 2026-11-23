import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpectralResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterOfSpectralResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearityResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyResultOfHodgeTateKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointResultOfFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvergenceResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartResultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestResultOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleResultStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem exists_family (hGram : GramSt) (hHom : HomSt) (hExt : ExtSt) (hSpec : SpecSt) (hChar : CharSt) (hGens : GensSt)
    (hLift : LiftSt) (hPt : PointSt) (hIso : IsoSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    [IsLocallyNoetherian Z.X] (hpq : 1 ≤ Dw.p + Dw.q) (S : Scheme.{0}) [IsIntegral S] (ρ : S ⟶ Z.X) (p : ℕ) [Fact p.Prime]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hK : CharZero S.functionField)
    (hζ : ∃ ζ : S.functionField, IsPrimitiveRoot ζ (p ^ 2))
    (hsplit : SplitK Z.t (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ 2))
    (hgp : ρ (genericPoint S) ∈ Set.range Z.j) (N : ℕ) (hrk : N = Module.finrank ℤ Dw.La) :
    ∃ (ch : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (y ≫ ρ) (p ^ 2)) (J : Matrix (Fin N) (Fin N) ℤ),
      IsUnit J.det ∧ (∀ y, Gens fun m => ch m y) ∧
      (∀ (U : S.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ Z.t.G.left)),
        IsTanBasis Z.t (R := Γ(S, U)) (hU.fromSpec ≫ ρ) e → ∃ h : Fin N → Fin g → Γ(S, U), ChartDlog ch hU e h) ∧
      ∀ (y : Sp ↥(intO ℂ_[p]) ⟶ S) (K : Type) [Field K] (k : K →+* ℂ_[p]) (z₀ : Sp K ⟶ Xo.XF c),
        (∀ a : K, IsAlgebraic ℤ a) → spMap (intO ℂ_[p]).subtype ≫ y ≫ ρ = spMap k ≫ z₀ ≫ Z.j →
        Isotropic (fun m => ch m y) J := by
  classical
  haveI : CharZero S.functionField := hK
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  haveI := GlobalTheory.DetHT.mono_j_int Z
  have hq : p ^ 2 ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) =
      S.fromSpecStalk (genericPoint S) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)
  obtain ⟨ξ₀, hξ₀⟩ := GlobalTheory.DetHT.exists_lift_int Z (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (by
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum S.functionField) _ _
    exact ((Scheme.Hom.comp_apply _ _ _).trans (congrArg ρ Scheme.fromSpecStalk_closedPoint)).symm ▸ hgp)
  obtain ⟨s, ζ, B, hζp, hB, hG, hsg⟩ := hGram E H Dw l Xo c _ _ Z S.functionField ξ₀ (p ^ 2) hq hζ (hξ₀ ▸ hsplit) N hrk
  obtain ⟨χ, hχ, hχg⟩ := hHom E H Dw l Xo c _ _ Z S.functionField ξ₀ _ hξ₀ (p ^ 2) hq N s ζ B hζp hB hG hsg
  have key (s : S) := by
    haveI := (hN s).1
    haveI := (hN s).2
    exact GlobalTheory.T.integral_point_extension_split E H Z.X Z.t S.functionField _ (p ^ 2) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)
  have hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) :
      spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)
  have L (y : Sp ↥(intO ℂ_[p]) ⟶ S) := (key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ)
    inferInstance (hz y)
  let ch : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (y ≫ ρ) (p ^ 2) :=
    fun j y => Classical.choose ((L y).1 (χ j))
  have hc (j : Fin N) (y : Sp ↥(intO ℂ_[p]) ⟶ S) := Classical.choose_spec ((L y).1 (χ j))
  have memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S)
      (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]
    exact ⟨_, rfl⟩
  have hBJ : B.transpose * B.transpose⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  refine ⟨ch, B.transpose⁻¹, Matrix.isUnit_det_of_left_inverse hBJ, fun y => ?_, fun U hU g e he => ?_,
    fun y K _ k z₀ hK hy => ?_⟩
  · haveI := (hN (y (IsLocalRing.closedPoint _))).1
    haveI := (hN (y (IsLocalRing.closedPoint _))).2
    exact hGens E H Z.X Z.t S.functionField _ (p ^ 2) hq hζ hsplit _ _ (hgen _) p _ _ inferInstance (hz y) N χ _ hχg
      fun m => hc m y
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
      GlobalTheory.T.integral_point_torsion_split E H Z.X Z.t S.functionField _ p 2 hsplit Γ(S, U) (hU.fromSpec ≫ ρ) hchart g e he.1 (χ j)
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
    have k : DlogIs Z.t p 2 (ch j y) (fun i => spMap (dualMap ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ e i)
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
        rw [sp_comp, sp_comp, Category.assoc, Category.assoc, hr, hψ', hω]
        exact congrArg (_ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e))
    have h4 : (algebraMap (S.presheaf.stalk b) S.functionField).comp r = algebraMap (S.presheaf.stalk a) S.functionField :=
      congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkSpecializes_comp S.presheaf _ _)
    have hinj := IsFractionRing.injective (S.presheaf.stalk b) S.functionField
    choose s' hs' hs'' using fun m => hExt E H Dw l Xo c _ _ Z _ _ x₀ ξ₀ h1 (p ^ 2) hq (s m) (hG.1 m)
    let o : Over.mk (spMap k ≫ z₀) ⟶ Over.mk x₀ := Over.homMk (spMap ψ') h2
    obtain ⟨ζ₀, hζ₀⟩ := GlobalTheory.HtChar.root_mem (R := S.presheaf.stalk b) hq
      (u := (ζ : S.functionField)) (by rw [← Units.val_pow_eq_pow_val, hζp.pow_eq_one, Units.val_one])
    have hp₀ : IsPrimitiveRoot ζ₀ (p ^ 2) :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap _ S.functionField)
        (by rw [hζ₀]; exact IsPrimitiveRoot.coe_units_iff.2 hζp) hinj
    let ζ' := (hp₀.isUnit hq).unit
    have hζ' : Units.map (algebraMap (S.presheaf.stalk b) S.functionField).toMonoidHom ζ' = ζ := Units.ext hζ₀
    refine hIso E H Dw l Xo c _ _ Z p _ (spMap k ≫ z₀) (hPt E H Dw l Xo c Z hpq p K k z₀ hK _ _ rfl (by
      rw [hy, Category.assoc])) N hrk (fun m => o ≫ s' m) (Units.map ψ'.toMonoidHom ζ') B _
      (IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.HtChar.prim_map ψ' hq hp₀)) hBJ ⟨fun m => ?_, fun m m' => ?_⟩ _ fun m => ?_
    · rw [← MonObj.comp_pow, hs', MonObj.comp_one]
    · rw [← map_zpow]
      refine hSpec E H Dw l Xo c _ _ Z _ _ _ _ ψ' hinj x₀ ξ₀ _ (p ^ 2) hq (s' m) (s' m') (s m) (s m') _ _ (hs' m) (hs' m')
        (hs'' m).symm (hs'' m').symm rfl rfl _ ?_
      rw [map_zpow, hζ']
      exact hG.2 m m'
    · exact hChar E H Dw l Xo c _ _ Z S.functionField ξ₀ _ hξ₀ (p ^ 2) hq hζ hsplit _ _ (hgen a) _ r _ x₀ hinj h4
        (by rw [hx₀, ← Category.assoc, hr]) h1 p _ ψ' _ _ inferInstance h3 (hz y) h2 (s m) (s' m) _ (hs' m) (hs'' m).symm rfl
        (χ m) _ (hχ m) (hc m y)

theorem halfData_of (hChart : ChartSt) (hTest : TestSt) (hConv : ConvSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    [IsLocallyNoetherian X] {t : SAB H X} (hX : X.IsSeparated) {F : Type} [Field F] [NumberField F] {Y : Var F}
    {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) [hp : Fact p.Prime] (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X)
    (hρ : V.j ≫ ρ' = V.π ≫ ρ) {u₀ : Fin g → (Sp (DualNumber Y.Fn) ⟶ t.G.left)}
    {f : ∀ y : Y.X, Fin g → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {d : Y.X → Fin g → Y.Fnˣ}
    (hf : IsFlagFrame t ρ u₀ f d) (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W) (L : Fin g → LB V.X) (m : ℕ) (hm : 0 < m)
    (hLB : ∀ i, (L i).IsLB)
    (hL : ∀ i, NormsAt V (L i) p ⊤ (fun y => genAt (A i).D y ^ m) fun v e y => m * (A i).lg v e y)
    (hu : ∀ i y, UnitAt y (genAt (A i).D y * d y i))
    (hlg : ∀ i v, resP v = p → ∀ e y, (A i).lg v e y =
      Real.log (e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i))) + stepLog t ρ f p i v e y)
    (ch : Fin (g + g) → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ V.X, TorsChar t (y ≫ ρ') (p ^ 2))
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (hJ : IsUnit J.det) (hG : ∀ y, Gens fun m => ch m y)
    (hD : ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (n : ℕ) (e : Fin n → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)),
      IsTanBasis t (R := Γ(V.X, U)) (hU.fromSpec ≫ ρ') e → ∃ h : Fin (g + g) → Fin n → Γ(V.X, U), ChartDlog ch hU e h)
    (hI : ∀ (k : AlgebraicClosure F →+* ℂ_[p]) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G), below y.1 ∈ W →
      z ≫ V.π = y.1 → ∀ yO : Sp ↥(intO ℂ_[p]) ⟶ V.X, spMap (intO ℂ_[p]).subtype ≫ yO = spMap k ≫ z ≫ V.j →
      Isotropic (fun m => ch m yO) J) : HalfDataC A p := by
  classical
  choose cf hc₁ hc₂ hc₃ using hf.tri
  let T : Y.X → Matrix (Fin g) (Fin g) Y.Fn := fun y => Matrix.of fun k i => cf y i k
  have hT (y : Y.X) : (T y).BlockTriangular id := fun k i h => hc₂ y i k h
  have hTu (y : Y.X) : IsUnit (T y).det := by
    rw [Matrix.det_of_upperTriangular (hT y), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ h => (d y i).ne_zero ((hc₁ y i).symm.trans h)
  have hch : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (n : ℕ)
      (e : Fin n → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin (g + g) → Fin n → Γ(V.X, U))
      (M : Matrix (Fin (g + g)) (Fin g) V.G.functionField),
      x ∈ U ∧ IsTanBasis t (hU.fromSpec ≫ ρ') e ∧ ChartDlog ch hU e h ∧ ChartVal V ρ' f T hU e h M := by
    intro x
    obtain ⟨⟨U, hU⟩, n, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t V.X ρ' x
    obtain ⟨h, hh⟩ := hD U hU n e he
    obtain ⟨M, hM⟩ := hChart E H X t F Y V ρ' ρ hρ g u₀ f T hf.tan hTu hc₃ U hU n e he _ h
    exact ⟨U, hU, n, e, h, M, hx, he, hh, hM⟩
  choose U hU n e h M hx he hd hM using hch
  refine ⟨V, W, V.X, U, M, J, d, T, L, m, hJ, hW, hm, fun x _ => ⟨x, hx x⟩,
    fun i x _ => TopologicalSpace.Opens.mem_iSup.1 ((hLB i).cover.symm ▸ trivial : x ∈ ⨆ c, (L i).U c), fun y => ⟨hT y, hc₁ y⟩, hu, hL,
    fun a z hz k l => ?_, fun v hv ε y hy z yt hz hyt => ?_⟩
  · obtain ⟨α, b, -, -, hb⟩ := hM a z hz
    exact ⟨_, (hb k l).symm⟩
  subst hv
  have P := fun a b ha hb => hTest E H X t hX F Y V ρ' ρ hρ g f T hf.indep v ch J hG (U a) (U b) (hU a) (hU b) _ _ (e a) (e b)
    (h a) (h b) (M a) (M b) (he a) (he b) (hd a) (hd b) (hM a) (hM b) ε y z yt hz hyt ha hb (hI _ y z hy hz) _ rfl
  have h₀ : ⊤ ≤ yt ⁻¹ᵁ U (yt (IsLocalRing.closedPoint _)) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem yt (hx _)).ge
  have hpos := (P _ _ h₀ h₀).1
  have Q := fun a b ha hb => hConv F v ε g J _ _ _ hpos (P a b ha hb).2
  refine ⟨_, fun k _ => Real.exp_pos _, fun i => ?_, fun a ha => ⟨(Q a a ha ha).1, (Q a a ha ha).2.1, (Q a a ha ha).2.2.1,
    fun b hb => (Q a b ha hb).2.2.2⟩⟩
  rw [hlg i v rfl, Real.log_exp, Real.log_exp, add_sub_assoc, ← mul_sub,
    GlobalTheory.LineNorm.Chart.stepLog_eq ρ f (resP v) i v ε y hp.out _ rfl, decide_eq_true rfl]
  congr 2
  have h₁ := hpos i
  have h₂ := hpos (i + 1)
  have e₁ : (Finset.univ.filter fun l : Fin g => (l : ℕ) < i + 1) = insert i (Finset.univ.filter fun l : Fin g => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold wedgeNorm at h₁ h₂ ⊢
  rw [e₁, Finset.prod_insert (by simp)] at h₂ ⊢
  rw [Real.log_mul (left_ne_zero_of_mul h₂.ne') h₁.ne', add_sub_cancel_right]
  rfl

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F}
  (C : GlobalTheory.ShFam.FlagCpt Z ε)

theorem prod_expo (a : ℕ → Bool) (R : Option ℝ) (k : Fin (letters Dw).length) (y : C.Y.X) :
    ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x =
      dg C y ((letters Dw).get k).1 ((letters Dw).get k).2 := by
  have h : letterOf Dw (.inr k) = some ((letters Dw).get k) := List.getElem?_eq_getElem k.2
  rw [Finset.prod_eq_single ((letters Dw).get k) (fun x _ hx => by
    rw [expo_single, if_neg (by rw [h]; exact fun e => hx (Option.some.inj e).symm), zpow_zero]) (by simp),
    expo_single, if_pos h, zpow_one]

theorem halfData_flag (hGram : GramSt) (hHom : HomSt) (hExt : ExtSt) (hSpec : SpecSt) (hChar : CharSt) (hGens : GensSt)
    (hLift : LiftSt) (hPt : PointSt) (hIso : IsoSt) (hChart : ChartSt) (hTest : TestSt) (hConv : ConvSt) (hBun : BundleSt)
    [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (M₀ : GlobalTheory.TrueGeo.Model C.Y) (ρ₀ : M₀.X ⟶ Z.X)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₀.X) (hρ : M₀.j ≫ ρ₀ = C.π ≫ GlobalTheory.Toroidal.genι Z)
    (hpq : 1 ≤ Dw.p + Dw.q) {g : ℕ} (hg : (letters Dw).length = g) (hrk : g + g = Module.finrank ℤ Dw.La)
    {Cx : CxSt F} (hm : Mets C Cx) (a : ℕ → Bool) (ha : {q | a q = true}.Finite) (R : Option ℝ) (p : ℕ) [hp : Fact p.Prime]
    (hap : a p = true) :
    HalfDataC (fun k : Fin g => adlOf C hm (wholeSym a R (Sum.inl k : Fin g ⊕ Fin g))) p := by
  subst hg
  let w : Fin (letters Dw).length → (Sym E →₀ ℤ) := fun k => Finsupp.single (a, R, .inr k) 1
  obtain ⟨V₀, m, hm0, hV₀⟩ := hBun F C.Y _ (fun k => divOf C (expo Dw (w k))) (fun k => lgOf C (w k)) ⟨M₀, hM⟩ fun k =>
    fromModel_lgOf C GlobalTheory.ShFam.Pad.HTBound.htBound hX M₀ ρ₀ hM hρ (w k) fun b hb => by
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
      exact ha
  obtain ⟨V, b, b', ρ', e₀, e₁, e₂, e₃, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists _ _ _ Z.t _ _ M₀ ρ₀ V₀ (p ^ 2) (pow_ne_zero _ hp.out.ne_zero)
  rw [hρ] at e₄
  obtain ⟨L, hL⟩ := hV₀ V b b' e₀ e₁ e₂ e₃
  haveI := Z.jQ_open
  let W : C.Y.X.Opens := C.π ⁻¹ᵁ Z.jQ.opensRange
  have hW : genericPoint C.Y.X ∈ W := by
    letI := (GlobalTheory.ShFam.constF ε C.Y).toAlgebra
    refine ⟨GlobalTheory.AllWt.ptF C.y0 (IsLocalRing.closedPoint _), ?_⟩
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun q : Sp C.Y.Fn ⟶ _ => q (IsLocalRing.closedPoint _)) C.y0_x).trans ?_)
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg C.π Scheme.fromSpecStalk_closedPoint)
  have hrange (x : V.G) (hx : V.π x ∈ W) : ρ' (V.j x) ∈ Set.range Z.j := by
    obtain ⟨q, hq⟩ := hx
    refine ⟨q, ?_⟩
    rw [← Scheme.Hom.comp_apply, e₄, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hq]
    rfl
  have hgp : ρ' (genericPoint V.X) ∈ Set.range Z.j := by
    have h₁ : V.j (genericPoint V.G) = genericPoint V.X :=
      ((GlobalTheory.HtGen.SplitCover.j_gen_specializes V).antisymm (genericPoint_specializes _)).eq
    have h₂ : V.π (genericPoint V.G) = genericPoint C.Y.X := (V.φ_eq_fnMap.1.antisymm (genericPoint_specializes _)).eq
    rw [← h₁]
    exact hrange _ (h₂ ▸ hW)
  obtain ⟨ch, J, hJ, hG, hD, hI⟩ := exists_family hGram hHom hExt hSpec hChar hGens hLift hPt hIso Z hpq V.X ρ' p V.normal
    hz hζ hs hgp _ hrk
  have hu (i : Fin (letters Dw).length) (y : C.Y.X) : genAt (divOf C (expo Dw (w i))) y *
      (dg C y ((letters Dw).get i).1 ((letters Dw).get i).2 : C.Y.Fn) =
      ((∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (w i) x) * (eqn (divOf C (expo Dw (w i))) y)⁻¹ : C.Y.Fnˣ) := by
    rw [prod_expo, Units.val_mul, mul_comm, genAt]
  refine halfData_of hChart hTest hConv hX _ p V ρ' _ e₄ (isFlagFrame_concat C) W hW L m hm0 (fun i => (hL i).1)
    (fun i => (hL i).2 p)
    (fun i y => ?_) (fun i v hv e y => ?_) ch J hJ hG hD fun k y z hy hz yO hyO => ?_
  · have h₁ : (divOf C (expo Dw (w i))).IsEqn y (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (w i) x) :=
      isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
    refine (hu i y).symm ▸ ?_
    simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁
  · change lgOf C (w i) v e y = Real.log (e.w (valAt y.1 (genAt (divOf C (expo Dw (w i))) _ * _))) + _
    rw [hu, lgOf_eq_lgCopy, lgCopy_eq, mixLog_eq (b := a) (by simp [hv, hap])]
    congr 1
    refine (Finsupp.sum_single_index (h := fun (a : Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)).trans ?_
    simp only [symLog, mixLog, lnStep, dif_pos i.2, Int.cast_one, _root_.one_mul]
  · obtain ⟨z₀, hz₀⟩ := GlobalTheory.DetHT.exists_lift_int Z (z ≫ V.j ≫ ρ') (by
      rintro _ ⟨q, rfl⟩
      obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure F)) _ _
      refine hrange (below z) ?_
      rw [← hz] at hy
      exact hy)
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
    refine hI yO _ k z₀ (fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic x)) ?_
    rw [← Category.assoc, hyO, hz₀, Category.assoc, Category.assoc]

end Flags

end GlobalTheory.HalfGeo

open GlobalTheory.Mean4 GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published GlobalTheory.HalfGeo in

theorem GlobalTheory.HalfGeo.halfData_of_steps (hGram : GramSt) (hHom : HomSt) (hExt : ExtSt) (hSpec : SpecSt) (hChar : CharSt)
    (hGens : GensSt) (hLift : LiftSt) (hPt : PointSt) (hIso : IsoSt) (hChart : ChartSt) (hTest : TestSt) (hConv : ConvSt)
    (hBun : BundleSt) (D : Formalism.BasicNotions.D7) (O : Setup D) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (hp : p.Prime) (c : O.s.Comp) :
    HalfDataC (fun k : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
      (wholeSym (Function.update (ArIn.ind Sx) p true) (some R)
        (Sum.inl k : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))) p := by
  haveI := Fact.mk hp
  obtain ⟨hX, hN, M₀, ρ', hM, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hj := O.indef
  refine halfData_flag (O.Φ.C c) hGram hHom hExt hSpec hChar hGens hLift hPt hIso hChart hTest hConv hBun hX M₀ ρ' hM hρ
    (by omega) (length_letters O.S) ?_ _ _ ((insert p Sx).finite_toSet.subset fun q hq => ?_) _ p (Function.update_self ..)
  · rw [GlobalTheory.ZM.finrank_int_lattice, GlobalTheory.Proof.LetterConjugation.finrank_host, hpq, Nat.mul_div_cancel_left _ two_pos, two_mul]
  · by_cases h : q = p
    · simp [h]
    · simpa [Function.update_of_ne h, ArIn.ind, h] using hq

open GlobalTheory.Mean4 GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published GlobalTheory.HalfGeo in

theorem GlobalTheory.HalfGeo.halfData_whole : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    HalfDataC (fun k : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
      (wholeSym (Function.update (ArIn.ind Sx) p true) (some R)
        (Sum.inl k : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))) p :=
  fun h₂ _ _ _ D O _ Sx R _ p hp c => halfData_of_steps GlobalTheory.T.gram_matrix_result GlobalTheory.T.homomorphism_result GlobalTheory.T.extension_result GlobalTheory.T.spectral_result
    (GlobalTheory.T.character_of_spectral_result GlobalTheory.T.spectral_result) GlobalTheory.T.generators_result GlobalTheory.T.lifting_result (GlobalTheory.T.point_result_of_integrality GlobalTheory.T.integrality_result)
    (GlobalTheory.T.isogeny_result_of_hodge_tate_kernel GlobalTheory.T.integrality_result GlobalTheory.T.linearity_result (GlobalTheory.HTKernel.hodgeTateKernelAtPoint h₂)) GlobalTheory.T.chart_result
    (GlobalTheory.T.test_result_of_point (GlobalTheory.T.point_result_of_full GlobalTheory.T.full_result)) GlobalTheory.T.convergence_result GlobalTheory.T.vector_bundle_result D O Sx R p hp c

end
