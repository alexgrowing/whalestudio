import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodProper

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

theorem polAt_of_fibre {S Z : Scheme.{0}} {K : Type} [Field K] {t : SAB H S} {u : SAB H Z} {t' : SAB H (Sp K)}
    {x : Sp K ⟶ S} {y : Sp K ⟶ Z} (m : SABMap t' t x) (n : SABMap t' u y) (hp : IsProper u.G.hom)
    (hA : RelAmple u.G u.PP.L) (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) t.G x (pullback.fst t.G.hom x) := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m.φ = pullback.fst t.G.hom x ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G (𝟙 _) ψ :=
    m.cart.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have g₃ : IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _ ≫ y) (ψ ≫ n.φ) := g₂.comp n.cart
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull (ψ ≫ n.φ)) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) (pull_isLB u.PP.isLB _)
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ h₁.symm).symm
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap n) _ rfl)
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₃.1 hp
  have hq := amplePt Z K (𝟙 _ ≫ y) u.G ((Over.pullback x).obj t.G) _ g₃ u.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    u.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

theorem isProper_of_abLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  intro E _ _ _ H Dw l Xo T x t t' m₁ m₂ hab
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  have hW : GlobalTheory.LN.CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H T.V hW t
    (polAt_of_fibre m₂ m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv)
    (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (T.V ⧸ maximalIdeal T.V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (T.V ⧸ maximalIdeal T.V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick T.V (maximalIdeal T.V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (isAbelianScheme_of_unif_of_subsingleton l₁ l₂ T.V T.cpl P.D P.A t.G t.semi P.U hs).proper

end GlobalTheory.GoodProper
