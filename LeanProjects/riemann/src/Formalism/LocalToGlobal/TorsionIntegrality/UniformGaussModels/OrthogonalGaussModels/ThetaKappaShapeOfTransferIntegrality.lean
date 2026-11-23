import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OrthogonalShapeOneLetter
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.FourthPowerStandardLattice
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4
  LocalStandard KappaExists TransInt)

namespace AlgebraicValuationTrichotomy

theorem subst_rescale {K : Type} [Field K] (a : K) (f : PowerSeries K) {g : PowerSeries K}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.rescale a f) = PowerSeries.subst (PowerSeries.C a * g) f := by
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hX : PowerSeries.HasSubst (a • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hX hg']
  congr 1
  rw [← PowerSeries.coe_substAlgHom hg', map_smul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hg', PowerSeries.smul_eq_C_mul]

theorem ne_zero_of_norm {l : ℕ} [Fact l.Prime] {ε : MaximalUnramifiedExtension l} (hε : ‖ε‖ = 1) : (ε : ℂ_[l]) ≠ 0 := by
  intro h
  have h0 : ‖ε‖ = 0 := by
    rw [show ‖ε‖ = ‖(ε : ℂ_[l])‖ from rfl, h, norm_zero]
  rw [hε] at h0
  exact one_ne_zero h0

theorem symm_ne_zero {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {ε : MaximalUnramifiedExtension l} (hε : ‖ε‖ = 1) :
    ι.symm (ε : ℂ_[l]) ≠ 0 := by
  exact (map_ne_zero ι.symm).mpr (ne_zero_of_norm hε)

end AlgebraicValuationTrichotomy

open AlgebraicValuationTrichotomy

theorem lubin_tate_norm_exists : LTNormExists := by
  intro l _ L ι g2 g3 s2 ε c hc hε h2 h3 hs
  have he0 : ι.symm (ε : ℂ_[l]) ≠ 0 := symm_ne_zero ι hε
  have hιe : ι (ι.symm (ε : ℂ_[l])) = (ε : ℂ_[l]) := ι.apply_symm_apply _
  have hε0 : (ε : ℂ_[l]) ≠ 0 := ne_zero_of_norm hε
  have hc' : ι c ≠ 0 := (map_ne_zero ι).mpr hc
  have hlam : c * (ι.symm (ε : ℂ_[l]))⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero he0)
  refine ⟨c * (ι.symm (ε : ℂ_[l]))⁻¹, hlam, ?_⟩
  obtain ⟨-, -, -, -, -, -, hS, -, -, hG2, hG3⟩ := Formalism.L2.Th1.F.homogeneity L _ hlam
  obtain ⟨-, -, -, -, -, -, hS', -, -, hG2', hG3'⟩ := Formalism.L2.Th1.F.homogeneity L c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, hG2, hG2']
    simp only [map_mul, map_inv₀, map_pow, hιe]
    field_simp
  · rw [h3, hG3, hG3']
    simp only [map_mul, map_inv₀, map_pow, hιe]
    field_simp
  · rw [hs, hS, hS']
    simp only [map_mul, map_inv₀, map_pow, hιe]
    field_simp

theorem lubin_tate_transfer_integral : TransIntLT := by
  intro l _ hl L ι g2 g3 ε s2 hN hg2 hg3 hD hε hθ ω₀ hω hω2 s N hN0 hlN hs
  have he0 : ι.symm (ε : ℂ_[l]) ≠ 0 := symm_ne_zero ι hε
  have hιe : ι (ι.symm (ε : ℂ_[l])) = (ε : ℂ_[l]) := ι.apply_symm_apply _
  have hε0 : (ε : ℂ_[l]) ≠ 0 := ne_zero_of_norm hε
  obtain ⟨hlat, -, -, -, -, -, hS, -, -, hG2, hG3⟩ := Formalism.L2.Th1.F.homogeneity L _ he0
  obtain ⟨n2, n3, ns⟩ := hN
  have h2 : (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L _ he0).g₂ := by
    rw [hG2, map_mul, map_inv₀, map_pow, hιe, n2]
    field_simp
  have h3 : (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L _ he0).g₃ := by
    rw [hG3, map_mul, map_inv₀, map_pow, hιe, n3]
    field_simp
  have hs2 : (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L _ he0)) := by
    rw [hS, map_mul, map_inv₀, map_pow, hιe, ns]
    field_simp
  have hω' : ι.symm (ε : ℂ_[l]) * ω₀ ∈ (Formalism.L2.Th1.F.scalePair L _ he0).lattice := by
    rw [hlat, ← mul_assoc, inv_mul_cancel₀ he0, one_mul]
    exact hω
  have hω2' : ι.symm (ε : ℂ_[l]) * ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair L _ he0).lattice := by
    rw [hlat, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ he0, one_mul]
    exact hω2
  have hs' : (N : ℂ) * (ι.symm (ε : ℂ_[l]) * s) ∈ (Formalism.L2.Th1.F.scalePair L _ he0).lattice := by
    rw [hlat]
    convert hs using 1
    field_simp
  obtain ⟨V, hV, hVeq⟩ := ConjugatePartitionShape.factors l hl (Formalism.L2.Th1.F.scalePair L _ he0) ι g2 g3 ε s2 h2 h3 hs2
    hg2 hg3 hD hε hθ _ hω' hω2' N hN0 hlN _ hs'
  have hlp := Formalism.L2.Th1.D.BrC.logPair (K := ℂ_[l]) (show 2 ≤ l by omega)
  have hmap : ∀ T : PowerSeries ℂ, PowerSeries.rescale (ε : ℂ_[l]) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) T) =
      PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale (ι.symm (ε : ℂ_[l])) T) := by
    intro T
    ext n
    simp [PowerSeries.coeff_rescale, hιe]
  have hT : Formalism.L2.Th1.Top.thetaOne l (Formalism.L2.Th1.F.scalePair L _ he0) ι (ε : ℂ_[l])
      (ι.symm (ε : ℂ_[l]) * ω₀) (ι.symm (ε : ℂ_[l]) * s) =
      (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0
        (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))).subst (lgF ℂ_[l] l) := by
    rw [← ThetaHomothety.taylor0_scale L _ he0 ω₀ s, ← hmap]
    unfold Formalism.L2.Th1.Top.thetaOne
    rw [subst_rescale _ _ hlp.1]
  have hc : PowerSeries.constantCoeff (phL l g2 g3 s2 ε) = 0 := ConjugatePartitionShape.cc_ph l (by omega) g2 g3 s2 ε
  have hc' : MvPowerSeries.constantCoeff (-(phL l g2 g3 s2 ε)) = 0 := by
    rw [map_neg]
    exact neg_eq_zero.mpr hc
  rw [← hT, ← hVeq]
  change Formalism.L2.Th1.E.IntS (Formalism.DworkPowerSeriesWeights.mvExp (phL l g2 g3 s2 ε) * (Formalism.DworkPowerSeriesWeights.mvExp (-(phL l g2 g3 s2 ε)) * V))
  have key : Formalism.DworkPowerSeriesWeights.mvExp (phL l g2 g3 s2 ε) * Formalism.DworkPowerSeriesWeights.mvExp (-(phL l g2 g3 s2 ε)) = 1 := by
    have h1 := Formalism.L2.Th1.C.mvExp_add hc hc'
    rw [add_neg_cancel, Formalism.L2.Th1.C.mvExp_zero] at h1
    exact h1.symm
  rw [← mul_assoc, key, one_mul]
  exact hV

theorem local_kappa_shape_of_transfer_integrality (hT : TransIntLT) : uniformGaussModelConditionReformulated₂ := by
  intro l _ hl L ι g2 g3 ε s2 hN hg2 hg3 hD hε hθ ω₀ hω hω2 n _ _ h Λ α β g hS hidx e he θ hθ' htens
    t N hN0 hlN ht σ γ B' hF
  exact Formalism.L2.Th1.H.quadraticSemicharacters_fact l L ι ω₀ _ _ (phL l g2 g3 s2 ε)
    (Formalism.L2.Th1.D.BrC.logPair (K := ℂ_[l]) (show 2 ≤ l by omega))
    (ConjugatePartitionShape.cc_ph l (by omega) g2 g3 s2 ε)
    (hT l hl L ι g2 g3 ε s2 hN hg2 hg3 hD hε hθ ω₀ hω hω2) n h Λ α β g hS hidx e he θ hθ' htens
    t N hN0 hlN ht (MaximalUnramifiedExtension l) (MaximalUnramifiedExtension l).subtype γ B' hF.2

theorem theta_kappa_shape_of_transfer_integrality (hT : TransIntLT) : uniformGaussModelConditionEquivalent := by
  intro hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hok n _ _ h Λ g₀ hLat
  obtain ⟨κ, hκ0, hκa, hκn, hrest⟩ := Formalism.L2.Th1.H.quadraticSemicharacters_of_fact hL hκ a₀ b₀ c₀ dK ha hdK lam hlam hok n h Λ g₀
    hLat.1 hLat.2.1 hLat.2.2.1 hLat.2.2.2.1 hLat.2.2.2.2
  refine ⟨κ, hκ0, hκa, hκn, ?_⟩
  intro θ hθ htens l _ hl ι
  obtain ⟨g₁, hI, hidx, -, -, hsh⟩ := hrest θ hθ htens l ι
  refine ⟨g₁, hI, hidx, ?_⟩
  intro g2 g3 ε s2 hN hg2 hg3 hD hε hth t N hN0 hlN ht σ γ B' hF
  have hH := Formalism.L2.Th1.F.homogeneity (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) lam hlam
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
    unfold cmL
    rw [hH.1, inv_mul_cancel_left₀ hlam]
    exact (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK).ω₁_mem_lattice
  have hω2 : lam * (a₀ : ℂ) / 2 ∉ (cmL a₀ b₀ dK ha hdK lam hlam).lattice := by
    unfold cmL
    rw [hH.1, mul_div_assoc, inv_mul_cancel_left₀ hlam]
    exact (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK).ω₁_div_two_notMem_lattice
  exact hsh (lgF ℂ_[l] l) (expF ℂ_[l] l) (phL l g2 g3 s2 ε)
    (BrC.logPair (by omega)) (ConjugatePartitionShape.cc_ph l (by omega) g2 g3 s2 ε)
    (hT l hl _ ι g2 g3 ε s2 hN hg2 hg3 hD hε hth (lam * a₀) hω hω2)
    t N hN0 hlN ht (MaximalUnramifiedExtension l) (MaximalUnramifiedExtension l).subtype γ B' hF.2

end Formalism.L2.Th1.Top
