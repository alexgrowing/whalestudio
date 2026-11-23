import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDimStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.DivPotGood

theorem potGood_of_divisionAlgebra_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hact h1 hmul hadd B _ _ _ jj hdiv hinj hspan hgB
  obtain ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, hsa, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, ?_⟩

  set f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  set A' := (Over.pullback f).obj A
  have hψ : IsGrpPullback A' A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨act₁, ⟨h1a, h1b, h1c, h1d⟩, -⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes (Sp K) (Sp L) f A A' _ hψ O act hact h1 hmul hadd
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hmod A' _ hψ
  obtain ⟨act₂, ⟨h2a, h2b, h2c, h2d⟩, -⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G A' φ hsa hφ O act₁ h1a h1b h1c h1d
  have hres : IsGrpPullback (GlobalTheory.SS.spFibre G) G (spMap (IsLocalRing.residue W)) (pullback.fst G.hom _) :=
    isGrpPullback_pullback G _
  obtain ⟨act₃, ⟨h3a, h3b, h3c, h3d⟩, -⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (IsLocalRing.residue W)) G (GlobalTheory.SS.spFibre G) _ hres O act₂ h2a h2b h2c h2d
  have hsa₀ : IsSemiAbelian (GlobalTheory.SS.spFibre G) := IsSemiAbelian.pullback _ G hsa
  haveI := hsa₀.comm
  obtain ⟨ρ, -⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action _ (GlobalTheory.SS.spFibre G) E O act₃ h3a h3b h3c h3d

  obtain ⟨e, -⟩ := hmod
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hA'g : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom f) hg
  have hGLg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (snd := ((Over.pullback (spMap (algebraMap W L))).obj G).hom)
        (f := A'.hom) (g := 𝟙 _) ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩) hA'g
  have hsc : GlobalTheory.SS.SmConn G := ⟨hsa.comm, hsa.smooth, hsa.separated, hsa.quasiCompact, hsa.geomConnected⟩
  have hsp : SmoothOfRelativeDimension g (GlobalTheory.SS.spFibre G).hom := GlobalTheory.IsogRed.relDim_spFibre (K := L) G hsc g hGLg
  have hle := GlobalTheory.T.finrank_torusExtension_characters_le_relDim _ (GlobalTheory.SS.spFibre G) E g hsp
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  have h0 : Module.finrank ℤ E.X = 0 := GlobalTheory.T.divisionAlgebra_order_no_small_lattice B O jj hdiv hinj hspan E.X ρ (lt_of_le_of_lt hle hgB)

  have hprop : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom f))
    rw [← Over.w e.hom]
    infer_instance
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsa hprop E h0

end GlobalTheory.DivPotGood
