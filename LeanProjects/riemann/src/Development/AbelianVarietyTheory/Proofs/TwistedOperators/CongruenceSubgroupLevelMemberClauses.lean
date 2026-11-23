import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointMemCongruenceSubgroupOffPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

set_option maxHeartbeats 4000000 in

theorem congLev_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  intro D c s 𝔪 h𝔪 hS hsd hJ
  have hΛ : Submodule.IsLattice D.host.E s.Λ := hsd.1
  obtain ⟨β, hβ⟩ := frame_exists_alt D.host.F D.host.E s.V.rank s.Λ hΛ
  have memJ : ∀ k, k ∈ s.J ↔ k ∈ GfC s.V ∧ Lev.finE s.V k ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 := by
    intro k; rw [hJ]; exact Iff.rfl
  have toSt : ∀ x, x ∈ congLev D.sp.cm s.V.gram s.Λ 𝔪 → x ∈ Formalism.L2.DIV.St β := fun x hx =>
    (GlobalTheory.LevSplit.mem_St_iff β s.Λ hβ x).2 (stab_of_mem_congLev hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; exact ((memJ k).1 hk).1
  · exact ⟨(congLev D.sp.cm s.V.gram s.Λ 𝔪).comap (Lev.finE s.V), (GlobalTheory.FunObj.congLev_open_compact s.V hΛ h𝔪).1,
      fun k hk hkf => (memJ k).2 ⟨hkf, hk⟩⟩
  · intro k hk v
    exact (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V β s.Λ hβ k).1 (toSt _ ((memJ k).1 hk).2) v
  · intro k hkf hint h1
    exact (memJ k).2 ⟨hkf, GlobalTheory.T.finitePoint_mem_congruenceSubgroup_offPlaces D s.V c.S 𝔪 h𝔪 hS k hkf hint h1⟩
  · intro P hP
    obtain ⟨T1, T2, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨e, f, hi⟩ := T2 P
    refine ⟨e, f, hi, fun g hg => ?_, fun _ _ _ => rfl⟩
    obtain ⟨hff, hcf, -, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, -, -⟩ := T1 f hff hcf
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hL0 : Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub s.V) = Formalism.L2.Herm.hatL (F := D.host.F) s.Λ := by
      congr 1; exact SetLike.coe_injective (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice s.V)
    rw [GlobalTheory.LevSplit.ksph_iff, hL0, SetLike.mem_coe, memJ]
    constructor
    · rintro ⟨hG, hK⟩
      exact ⟨hG, stab_of_mem_congLev hK⟩
    · rintro ⟨hG, h1, h2⟩
      have s1 := GlobalTheory.LevSplit.supp_fin s.V hg
      have s2 := GlobalTheory.LevSplit.supp_fin s.V ((hLf _).1 (Lf.inv_mem ((hLf _).2 hg)))
      rw [MonoidHom.map_inv] at s2
      rw [← hu] at s1 s2
      refine ⟨hG, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V g) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ s1.symm h1
      · exact cong_of_eq s.Λ ha u _ _ s2.symm h2
  · intro P e f hP hi k hk
    obtain ⟨T1, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V
    obtain ⟨hff, hcf, hG, -⟩ := T3 P e f hi
    obtain ⟨⟨Lf, hLf⟩, hsplit, -⟩ := T1 f hff hcf
    obtain ⟨⟨Lf', hLf'⟩, -, -⟩ := T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero])
      (by rw [RingHom.map_sub, RingHom.map_one, hcf])
    obtain ⟨k₁, k₂, h1, h2, hk12⟩ := hsplit k
    obtain ⟨a, ha, u, hu⟩ := exists_idem_eq h𝔪 hS hP hi
    have hinv : SuppF s.V f k₁⁻¹ := (hLf _).1 (Lf.inv_mem ((hLf _).2 h1))
    have hinv' : SuppF s.V (1 - f) k₂⁻¹ := (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 h2))
    have hφφ : GlobalTheory.LevSplit.finSw D f * GlobalTheory.LevSplit.finSw D f = GlobalTheory.LevSplit.finSw D f := by
      rw [← RingHom.map_mul, hff]
    rw [← hu] at hφφ
    have s1 := GlobalTheory.LevSplit.supp_fin s.V h1
    have s1' := GlobalTheory.LevSplit.supp_fin s.V hinv
    have s2 := GlobalTheory.LevSplit.supp_fin s.V h2
    have s2' := GlobalTheory.LevSplit.supp_fin s.V hinv'
    rw [MonoidHom.map_inv] at s1' s2'
    rw [RingHom.map_sub, RingHom.map_one] at s2 s2'
    rw [← hu] at s1 s1' s2 s2'
    obtain ⟨-, hkK⟩ := (memJ k).1 hk
    have hK' := stab_of_mem_congLev hkK
    have ek : Lev.finE s.V k = Lev.finE s.V k₁ * Lev.finE s.V k₂ := by rw [hk12, MonoidHom.map_mul]
    have m1 : k₁ ∈ s.J := by
      refine (memJ k₁).2 ⟨hG k₁ h1, mem_congLev_of _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA s.V k₁) ?_ ?_⟩
      · exact cong_of_eq s.Λ ha u _ _ (comp_sub_one _ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul]))) hK'.1
      · exact cong_of_eq s.Λ ha u _ _
          (comp_sub_one _ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, _root_.mul_inv_rev, Units.val_mul]))) hK'.2
    refine ⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩
    have : k₂ = k₁⁻¹ * k := by rw [hk12, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk

end GlobalTheory.CongMember
