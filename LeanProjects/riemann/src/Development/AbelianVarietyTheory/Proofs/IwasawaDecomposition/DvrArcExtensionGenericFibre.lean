import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionSpecialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionValuationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

open GlobalTheory.ArcBuild in

theorem GlobalTheory.ArcBuild.exists_arcIn_hasArcData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → Nontrivial P.D.toPre.X → ∀ ϖ : T.V, Irreducible ϖ → (∀ Q : P.D.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ P.D.toPre ϖ Q → ∀ u v, (2 * l.M' : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf P.D.toPre Q u v) → GlobalTheory.ArcExt.LevelReps Y y t m P → ∃ a : ArcIn D l β T.V b, Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z h₁ h₂ h₃ h₄ t m P hP hX ϖ hϖ hdiv hL
  have hdiv' : ∀ a a', (2 * l.M' : ℤ) ∣ beF P hϖ a a' := fun a a' => hdiv _ (isQ_qv P hϖ) a a'
  have hLie : LieCl P D β b := by
    intro F _ _ _ r hr τ
    have hf : Function.Injective ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V (FractionRing T.V))) :=
      (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
    exact GlobalTheory.LieUnif.lieMult_unif E H T t P F _ hf τ _ (GlobalTheory.T.dvr_arc_extension_residue E H D l Xo c O β Y T io b y z h₁ h₂ h₃ h₄ t m F r hr τ)
  exact ⟨arc P hϖ Y b y m hX hdiv' hL hLie (GlobalTheory.T.dvr_arc_extension_special E H D l Xo c O β Y T io b y z h₁ h₂ h₃ h₄ t m P hP ϖ hϖ hdiv' hL),
    GlobalTheory.T.dvr_arc_extension_valuation E H D l Xo c O β Y T io b y z h₁ h₂ h₃ h₄ t m P hX ϖ hϖ hdiv' hL hLie _⟩
