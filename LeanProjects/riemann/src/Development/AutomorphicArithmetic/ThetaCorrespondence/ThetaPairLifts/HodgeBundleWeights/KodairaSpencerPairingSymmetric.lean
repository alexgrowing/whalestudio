import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLiftStatement

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers TensorProduct TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CrysConn
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSSym
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X ⟶ Sp (DualNumber R)}
open GlobalTheory.Published
end GlobalTheory.KSSym
namespace GlobalTheory.KSSym
open NumberField Formalism.L2.Pj MonObj
theorem kodairaSpencer_map_symm : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X)
    (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)),
    IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
    GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ →
    ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' →
      ψ f k' + ψ k g = 0 := by
  rintro Pr E _ _ _ H Dw l Xo K _ x x' A _ A' _ π π' i h ψ hπ hπ' rfl hψ f g k k' ⟨d, hd, ed⟩ ⟨d', hd', ed'⟩
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨ψ', hψ', iso, -⟩ := GlobalTheory.PolExistsRing.polForm_exists Pr.p5 Xo hπ'
  rw [← snd_polForm Pr.p5 hA gA h Xo.univ.t.PP.isLB hψ hψ' ed ed', iso _ hd _ hd']
  rfl
end GlobalTheory.KSSym
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)), IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' → ψ f k' + ψ k g = 0 := by
  first | exact @_root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | exact _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | (intros; apply _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm <;> assumption)
end
