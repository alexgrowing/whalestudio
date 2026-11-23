import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForallStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAllStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

theorem suppSecond_holds : ∀ D : D7, SuppSecond D := by
  intro D k _ _ _ _ ι p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL Λ P a b a' sh sd₂ Φ₁ Φ₂ hΦ₁ hΦ₂
  have tameP : ∀ v, P v → Tame D v := fun v hv => (sh.good v hv).tame
  refine ⟨?_, fun h₁ hh₁ => ⟨?_, ?_⟩⟩
  · exact GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ P
      (fun v hv => ⟨(sh.good v hv).sdW, sd₂, tameP v hv, (sh.unr v hv).2.1, (sh.unr v hv).2.2⟩) Φ₂ hΦ₂
  · intro h₂ hh₂
    exact GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ P (fun v hv => ⟨sh.adapt v hv, (sh.unr v hv).2⟩) Φ₂ hΦ₂
      h₁ hh₁ h₂ hh₂
  · intro g hg φ hφ h₂ hne
    have key := GlobalTheory.T.placewise_to_adelicDecomposition_forall D B'.V Λ.L₂ P sd₂ (besGrp B'.d B'.o) h₂ ?_
    · exact key
    intro v hv
    obtain ⟨hv', hhv, h', hh', rfl⟩ := GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace D B'.V h₂ v
    refine ⟨hv', hhv, h', hh', rfl, ?_⟩
    have gd := sh.good v hv
    have ad := sh.adapt v hv
    have sdL₁ : IsSelfDualC J.W Λ.L₁ := gd.sdW

    have hΦ₂v : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) Φ₂ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ P tameP Φ₂).1.mp hΦ₂).2 v hv
    set f := s₂.om (h₁, h') Φ₂ with hfdef
    have hf : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) f :=
      (GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ (· = v)
        (fun w hw => hw ▸ gd.tame) Φ₂).2.1 hΦ₂v h₁ (GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone D J.W P (· = v) (fun w hw => hw ▸ hv) hh₁) h' hh'

    set Ξ₁ := flatBF s₁ (s₁.om (g, h₁) Φ₁) with hΞ₁def
    have hΞ₁P : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ :=
      ((GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D ψ (σ + 1) B J s₁ Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ P (fun w hw => sh.good w hw)
        (fun w hw => (sh.unr w hw).1) sdL₁ Φ₁ hΦ₁).2 g hg).2 h₁ hh₁
    have hΞ₁ : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ (· = v) Ξ₁ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s₁.χV s₁.χW s₁.om₀ s₁.weil₀ Λ.M₀ Λ.M₁ gd.sdV₀ gd.sdW₀ P tameP Ξ₁).1.mp
        hΞ₁P).2 v hv

    have hom : s₂.om (h₁, hv' * h') Φ₂ = s₂.om (1, hv') f := by
      rw [hfdef, show ((h₁, hv' * h') : GA D J.W × GA D B'.V) = (1, hv') * (h₁, h') by simp, map_mul]
      rfl
    have hand_eq : Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (hv' * h') =
        hand0 s₁ s₂ l vL φ Ξ₁ (flatFB s₂ (s₂.om (1, hv') f)) := by
      simp only [Chain.hand, hand0, hom, hΞ₁def]
    rw [hand_eq] at hne
    have hne' : flatFB s₂ (s₂.om (1, hv') f) ≠ 0 := by
      intro h0
      apply hne
      rw [h0, show (0 : WO J.W₀ B'.V₀ → ℂ) = (0 : ℂ) • (0 : WO J.W₀ B'.V₀ → ℂ) by simp, GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, zero_smul]
    obtain ⟨nn, hnF, hnv, γ, hγ, κ, hκ, hdec, hγp⟩ :=
      (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v ad (sh.unr v hv).2 (flatFB s₂)
        ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B' s₂) ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B' s₂) f hf).2 hv' hhv hne'
    by_cases hgl : ∃ i, v = (p i).v
    · obtain ⟨i, rfl⟩ := hgl
      rcases GlobalTheory.T.threeOrbits_gluedCore_atPlace D k (p i) n'' q σ B' Λ.M₂ (a'.α i) (a'.α₀ i) (a'.P i) ad.sdW₀ (sh.gl' i) γ hγ hγp with
        ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ | ⟨Λ₀, hΛ₀, hmov⟩
      · obtain ⟨r, hr, hrv, κ', hκ', heq⟩ :=
          GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ (p i).v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
        exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩
      · exfalso
        apply hne
        obtain ⟨M, sdM, hMov, hvacM⟩ :=
          GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ (p i).v ad (sh.unr _ hv).2 f hf γ hγ
        have hlat : (a'.α₀ i).IsLat M (lastKer Λ₀) ∨ (a'.α₀ i).IsLat M (lastPair q Λ₀).lat := by
          rcases hmov with h | h
          · exact Or.inl (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
          · exact Or.inr (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
        obtain ⟨φf, hφf, hφP⟩ := hφ.2 i
        have hz := GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice D k (p i) n n' n'' q ψ σ B J B' s₁ s₂ l vL s₂.weil.std (sh.unr _ hv).1
          (sh.unr _ hv).2 Λ.M₀ Λ.M₁ M (a.α i) (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (a.P i) (b.Q i) Λ₀ gd.sdV₀ gd.sdW₀
          sdM (sh.gl i) (sh.mid i) (sh.gl' i).sum hlat Ξ₁ _ hΞ₁ hvacM φf hφf
        rw [hφP] at hz
        rw [hdec, GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar D ψ σ J B' s₂ Λ.L₁ Λ.L₂ (p i).v sdL₁ sd₂ gd.tame (sh.unr _ hv).2 f hf nn hnF hnv _ κ hκ,
          GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, hz, smul_zero]
    · obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split D σ B' Λ.M₂ v gd.tame ad.sdW₀
        (sh.split v hv fun i h => hgl ⟨i, h⟩) γ hγ hγp
      obtain ⟨r, hr, hrv, κ', hκ', heq⟩ := GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
      exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.FinPl
