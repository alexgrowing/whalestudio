import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtNZ

theorem exists_sec_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  intro E _ _ _ H R _ _ _ hB t ⟨P⟩
  haveI := t.comm
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IsNoetherianRing R := hB.1.1
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R P.D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : P.D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good P.D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) P.D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract P.D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit P.D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫
        padd P.D.toPre.P.A (snd _ _) (toUnit _ ≫ P.D.toPre.c 0) = padd P.D.toPre.P.A (𝟙 _) (toUnit _ ≫ P.D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ P.D.toPre.c 0 = toUnit _ ≫ P.D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit P.D.toPre.P.A) (𝟙 P.D.toPre.P.A) ≫ toUnit _ ≫ η[P.D.toPre.P.A] = toUnit _ ≫ η[P.D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : P.D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) P.D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl P.U f₀ ⟨_, hx, hxn⟩
  have key : ∃ σ : H0 P.U.LG.L 1, ∃ g, t.G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    ⟨σ, GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl P.U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem⟩
  rw [P.bundle] at key
  obtain ⟨σ, g, hg, hn⟩ := key
  refine ⟨GlobalTheory.TorRef.upSec t.G σ, GlobalTheory.Ex.OnModel.toBase t.G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase t.G ≫ (fst (Over.mk (𝟙 (Sp R))) t.G).left = t.G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ExtNZ
