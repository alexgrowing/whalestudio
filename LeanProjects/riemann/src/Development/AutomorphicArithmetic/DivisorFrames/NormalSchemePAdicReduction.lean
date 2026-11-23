import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.SplitTorsionLabelsExist
import Development.AutomorphicArithmetic.DivisorFrames.TorsionLabelsOnSeparatedModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.normal_scheme_p_adic_reduction :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (S : Scheme.{0}) [IsIntegral S] (ρ : S ⟶ Z.X) (y₀ : Sp S.functionField ⟶ Xo.XF c) (p : ℕ) [Fact p.Prime] (n : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → CharZero S.functionField → (∃ ζ : S.functionField, IsPrimitiveRoot ζ (p ^ n)) → GlobalTheory.HtGen.SplitK Z.t (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) → S.fromSpecStalk (genericPoint S) ≫ ρ = y₀ ≫ Z.j → LabFam Z ρ p n := by
  intro E _ _ _ H Dw l Xo c Z _ hsep S _ ρ y₀ p _ n hN hK hζ hsplit0 hξ
  classical
  haveI : CharZero S.functionField := hK
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hsplit : GlobalTheory.HtGen.SplitK Z.t (K := S.functionField) (y₀ ≫ Z.j) (p ^ n) := hξ ▸ hsplit0
  have hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) =
      y₀ ≫ Z.j := by
    rw [← hξ, ← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)
  have key (s : S) := by
    haveI := (hN s).1
    haveI := (hN s).2
    exact GlobalTheory.T.integral_point_extension_split E H Z.X Z.t S.functionField _ (p ^ n) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)
  obtain ⟨lb, ζ, hlb, χ, hχ⟩ := UpperTheory.split_torsion_labels_exist E H Dw l Xo c Z S.functionField y₀ (p ^ n) hq hζ hsplit
  have hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) :
      spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)
  have L (y : Sp ↥(intO ℂ_[p]) ⟶ S) := (key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ)
    inferInstance (hz y)
  let ch : Dw.La → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (y ≫ ρ) (p ^ n) :=
    fun j y => Classical.choose ((L y).1 (χ j))
  have hc (j : Dw.La) (y : Sp ↥(intO ℂ_[p]) ⟶ S) := Classical.choose_spec ((L y).1 (χ j))
  have memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S)
      (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]
    exact ⟨_, rfl⟩
  refine ⟨ch, fun x y hy => ?_, fun U hU g e he => ?_⟩
  · haveI := (hN (x (IsLocalRing.closedPoint _))).1
    haveI := (hN (x (IsLocalRing.closedPoint _))).2
    exact UpperTheory.torsion_labels_on_separated_model E H Dw l Xo c Z hsep S.functionField y₀ (p ^ n) hq hsplit lb ζ hlb χ hχ
      (S.presheaf.stalk (x (IsLocalRing.closedPoint _))) _ (hgen _) p (Scheme.stalkClosedPointTo x).hom (x ≫ ρ) y
      inferInstance (hz x) hy (fun a => ch a x) (fun a => hc a x)
  · by_cases hne : Nonempty U
    swap
    · exact ⟨fun _ _ => 0, fun x y hxy _ => absurd ⟨⟨_, memU U hU x y hxy⟩⟩ hne⟩
    haveI : IsIntegrallyClosed Γ(S, U) := GlobalTheory.LineNorm.Chart.isIntegrallyClosed_sections hN hU
    haveI := functionField_isFractionRing_of_isAffineOpen S U hU
    have hgU : genericPoint S ∈ U := by
      obtain ⟨u⟩ := hne
      exact (genericPoint_specializes u.1).mem_open U.isOpen u.2
    have hchart : spMap (algebraMap Γ(S, U) S.functionField) ≫ (hU.fromSpec ≫ ρ) = y₀ ≫ Z.j := by
      rw [← hξ, ← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hgU]
      rfl
    choose hh hhs using fun j : Dw.La =>
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
