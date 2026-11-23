import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTrivialOnPrincipal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEqOneOfSubOneMemValBallPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IndicatorIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneSubInvMemIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolumesNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfIsStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PFTSecFunOfNotMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusOfSubOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemCongruenceSubgroupOfEntries
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

namespace GlobalTheory.CompanionTheory.SmallSec

theorem torus : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ n₀ : ℕ,
  ∃ n : ℕ, n₀ ≤ n ∧ 1 ≤ n ∧ ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∃ C : ℂ, C ≠ 0 ∧
    (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → W2 ψ ν ν⁻¹ φ (dg2 a 1) = C) ∧
    (∀ a : Fˣ, (a : F) - 1 ∉ valBall F (n : ℤ) → W2 ψ ν ν⁻¹ φ (dg2 a 1) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ ν hν n₀
  obtain ⟨n, hn, hn1, hν1⟩ := GlobalTheory.CompanionTheory.CharTriv.exists_trivial_on_principal F ν hν n₀
  obtain ⟨hf, hg, hφ⟩ := GlobalTheory.CompanionTheory.TorSB.tor_schwartzBruhat F ψ hψ n hn1
  obtain ⟨hV, hH, -⟩ := GlobalTheory.CompanionTheory.VolNe.volumes_ne_zero F ψ
  have hν' : IsUnit1 ν⁻¹ := by
    refine ⟨hν.1.inv, fun x => ?_⟩
    have := hν.2 x
    simp [this]
  refine ⟨n, hn, hn1, _, hφ, (((selfDualMeasure ψ).real (valBall F (-(n : ℤ)) : Set F) : ℝ) : ℂ) * (((multHaar F).real {h : Fˣ | (h : F) - 1 ∈ valBall F (n : ℤ)} : ℝ) : ℂ), mul_ne_zero (Complex.ofReal_ne_zero.2 (hV _))
    (Complex.ofReal_ne_zero.2 (hH n hn1)), fun a ha => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ ν ν⁻¹ hν hν' _ hf _ hg a, ((GlobalTheory.CompanionTheory.KirTorus.torus_integral F ψ hψ ν n hn1 hν1 a).1 ha)]
    have h1 : mp a (1 / 2) = 1 := by
      simp [mp, GlobalTheory.CompanionTheory.SmallSec.modulus_eq_one_of_sub_one_mem_valBall_pos F n hn1 a ha]
    rw [h1]
    simp [hν1 a ha]
  · rw [GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ ν ν⁻¹ hν hν' _ hf _ hg a, ((GlobalTheory.CompanionTheory.KirTorus.torus_integral F ψ hψ ν n hn1 hν1 a).2 ha)]
    simp

theorem sec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (m : ℕ), 1 ≤ m →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  ∃ Φ ∈ LFS.SB F, ∃ c : ℂ, c ≠ 0 ∧
    (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
      LFS.Wp ψ W' Φ (GL2LocalData.em h) = c * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) ∧
    (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) →
      LFS.Wp ψ W' Φ (GL2LocalData.em h) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ W' m hm hW'
  obtain ⟨hV, -, hK⟩ := GlobalTheory.CompanionTheory.VolNe.volumes_ne_zero F ψ
  obtain ⟨h1, h0⟩ := GlobalTheory.CompanionTheory.SintSec.main F ψ hψ W' m hm hW' (secFun ψ m) (GlobalTheory.CompanionTheory.SmallSec.secFun_mem_SB_of_isStd F ψ hψ m) _
    (fun A ξ h => (GlobalTheory.CompanionTheory.SmallSec.pFT_secFun F ψ hψ m A ξ).1 h) (fun A ξ h => (GlobalTheory.CompanionTheory.SmallSec.pFT_secFun F ψ hψ m A ξ).2 h)
  exact ⟨secFun ψ m, GlobalTheory.CompanionTheory.SmallSec.secFun_mem_SB_of_isStd F ψ hψ m, _, mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hV _)))
    (Complex.ofReal_ne_zero.2 (hK m)), h1, h0⟩

end GlobalTheory.CompanionTheory.SmallSec
namespace GlobalTheory.CompanionTheory.SmallSec

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
  (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ U ∈ 𝓝 (1 : GL (Fin 2) F),
  ∃ W ∈ LFS.VF ψ (V2 ψ ν ν⁻¹), ∃ (S : Set (GL (Fin 2) F)) (C₁ : ℂ), IsOpen S ∧ (1 : GL (Fin 2) F) ∈ S ∧ S ⊆ U ∧ S ⊆ GL2LocalData.K2 F ∧ C₁ ≠ 0 ∧
    (∀ h, W (GL2LocalData.em h) ≠ 0 → ∃ x, ∃ u ∈ S, h = uni2 x * u) ∧
    ∀ x, ∀ u ∈ S, W (GL2LocalData.em (uni2 x * u)) = (ψ x : ℂ) * C₁ := by
  intro F _ _ _ _ _ _ ψ hψ ν hν U hU
  have hν' : IsUnit1 ν⁻¹ := by
    refine ⟨?_, fun x => ?_⟩
    · exact hν.1.inv
    · have := hν.2 x
      simp [this]
  obtain ⟨n₀, -, hn₀⟩ := (GLnLocal.hasBasis_nhds_one F 2).mem_iff.mp hU
  obtain ⟨n, hn, hn1, φ, hφ, C, hC, hc1, hc0⟩ := GlobalTheory.CompanionTheory.SmallSec.torus F ψ hψ ν hν n₀
  obtain ⟨V, hV⟩ := GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ ν ν⁻¹ hν hν' φ hφ
  obtain ⟨m', -, hm'⟩ := (GLnLocal.hasBasis_nhds_one F 2).mem_iff.mp
    (V.isOpen.mem_nhds V.one_mem)
  set W' := W2 ψ ν ν⁻¹ φ with hW'
  have hW'mem : W' ∈ V2 ψ ν ν⁻¹ := Submodule.subset_span ⟨φ, hφ, rfl⟩
  set m := max m' n with hm
  have hmm : ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g := fun g u hu =>
    hV g u (hm' (GLnLocal.congruenceSubgroup_antitone F 2 (le_max_left m' n) hu))
  have hm1 : 1 ≤ m := hn1.trans (le_max_right _ _)
  obtain ⟨Φ, hΦ, c, hc, hW1, hW0⟩ := GlobalTheory.CompanionTheory.SmallSec.sec F ψ hψ W' m hm1 hmm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.CompanionTheory.SmallSecSupp.support_and_value F ψ hψ W' (LFS.Wp ψ W' Φ) n m C c hn1 (le_max_right _ _)
    (GlobalTheory.CompanionTheory.WhittakerPsi.whittaker_upper_unipotent_equivariance ψ ν ν⁻¹ φ) hmm hc1 hc0 hW1 hW0
  refine ⟨LFS.Wp ψ W' Φ, Submodule.subset_span ⟨W', hW'mem, Φ, hΦ, rfl⟩,
    {u | u ∈ GLnLocal.congruenceSubgroup F 2 n ∧ u.val 1 0 ∈ valBall F (m : ℤ) ∧
      u.val 1 1 - 1 ∈ valBall F (m : ℤ)}, c * C, ?_, ?_, ?_, ?_, mul_ne_zero hc hC, ?_, ?_⟩
  · have h1 : IsOpen {u : GL (Fin 2) F | u.val 1 0 ∈ valBall F (m : ℤ)} :=
      (isOpen_valBall (m : ℤ)).preimage (GLnLocal.continuous_entry F 2 1 0)
    have h2 : IsOpen {u : GL (Fin 2) F | u.val 1 1 - 1 ∈ valBall F (m : ℤ)} :=
      (isOpen_valBall (m : ℤ)).preimage ((GLnLocal.continuous_entry F 2 1 1).sub continuous_const)
    exact (GLnLocal.isOpen_congruenceSubgroup F 2 n).inter (h1.inter h2)
  · refine ⟨one_mem _, ?_, ?_⟩ <;> simp
  · exact fun u hu => hn₀ (GLnLocal.congruenceSubgroup_antitone F 2 hn hu.1)
  · exact fun u hu => GLnLocal.congruenceSubgroup_le F 2 n hu.1
  · intro h hh
    obtain ⟨x, u, hu, rfl⟩ := hs1 h hh
    exact ⟨x, u, hu, rfl⟩
  · rintro x u ⟨h1, h2, h3⟩
    exact hs2 x u h1 h2 h3

end GlobalTheory.CompanionTheory.SmallSec
