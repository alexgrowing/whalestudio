import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGLStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatricesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGenericStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductorStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem hU_thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    hU D n v τ (thU D n v τ g) = GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
      (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) g := by
  unfold hU
  rw [Function.leftInverse_invFun (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).1 g]

theorem hU_isHgt (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsHgt (O := Ov D v) (nvL D v) (hU D n v τ) := by
  intro a d b κ
  obtain ⟨y, hy⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (pM a d b)
  obtain ⟨k, hk⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL κ)
  have hkK : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ k).2 ⟨κ, hk.symm⟩
  obtain ⟨hyP, hab⟩ := GlobalTheory.T.modulus_upper_parabolic_local D n v τ y a d b hy
  rw [← hy, ← hk, ← map_mul, hU_thU]
  exact (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) ⟨y, hyP⟩ hkK).trans hab

theorem rank_beta0 {k : Type} [Field k] {n r t : ℕ} (h : r + t = n) :
    (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : k) else 0).rank = r := by
  classical
  rw [Matrix.rank_diagonal]
  have hr : r ≤ n := by omega
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact Fintype.card_fin_lt_of_le hr

theorem psiV_lift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) (w : (Lv D v)ˣ) (ψ₀ : AddChar (kv D v) ℂ)
    (h : ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) =
      ψ₀ (IsLocalRing.residue (Ov D v) c))
    (ℓ : kv D v → Ov D v) (hℓ : ∀ a, IsLocalRing.residue (Ov D v) (ℓ a) = a) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (kv D v)) (T₀ : Matrix (Fin n) (Fin n) (Ov D v)) :
    psiV D.host.F ψ v (Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))) =
      ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
  have key : Matrix.trace ((((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y) * T₀.map (algebraMap (Ov D v) (Lv D v)))
      = ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  have key2 : Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v))) =
      IsLocalRing.residue (Ov D v) (Matrix.trace (Y.map ℓ * T₀)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, hℓ]
  rw [key, h, key2]

theorem split_place_rank_cut_of_local_computation : JpCondition → SplitPlaceRankCutEigenvalue := by
  intro hA D n r t hrt hr ψ hψ nb hnb v hgood τ
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ov D v)
  have hϖ0 : algebraMap (Ov D v) (Lv D v) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (Ov D v) (Lv D v))]
    exact hϖ.ne_zero
  obtain ⟨w, hw⟩ : ∃ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ := ⟨Units.mk0 _ hϖ0, rfl⟩
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := GlobalTheory.T.exists_residue_character_of_conductor D ψ v hgood ϖ hϖ w hw
  have hok := GlobalTheory.T.normalized_valuation_uniformizer D v ϖ hϖ w hw
  choose ℓ hℓ using fun a : kv D v => IsLocalRing.residue_surjective (R := Ov D v) a
  have hβ : (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0).rank = r := rank_beta0 hrt
  obtain ⟨ρ, hρ, hρs, hρm⟩ := GlobalTheory.T.surjective_reduction_maximal_compact D n v τ
  obtain ⟨c, hcd, hct, hcint⟩ := hA (Ov D v) (Lv D v) n r t hrt hr ψ₀ hψ₀ _ hβ
  choose f hinf hoff hfX _ using fun Y : Matrix (Fin n) (Fin n) (kv D v) =>
    GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ (((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y)
  have hfinj : Function.Injective f := by
    intro Y Y' hYY
    have h1 : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y =
        ((w⁻¹ : (Lv D v)ˣ) : Lv D v) • liftM (L := Lv D v) ℓ Y' := by
      rw [← hfX Y, ← hfX Y', hYY]
    funext i j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.Jp.liftM, Matrix.map_apply] at h2
    have h3 := IsFractionRing.injective (Ov D v) (Lv D v) (mul_left_cancel₀ (Units.ne_zero _) h2)
    rw [← hℓ (Y i j), ← hℓ (Y' i j), h3]
  have hsinf : ∀ x ∈ Finset.univ.image f, ∀ (w' : NumberField.InfinitePlace D.host.F) (i j : Fin n),
      (GlobalTheory.AdelicU.compInf D.host.F D.host.E w') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinf Y
  have hsoff : ∀ x ∈ Finset.univ.image f, ∀ (v' : Pl D), v' ≠ v → ∀ (i j : Fin n),
      (PositivityTheory.Rg.Rsw.L.cv D v') (x.1 i j) = 0 := by
    intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hoff Y
  refine ⟨⟨Finset.univ.image f, fun x => coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
    (Function.invFun f x), hsinf, hsoff⟩, c, ?_, hcd, hct, ?_⟩
  · intro β' hβ' hint
    have hTint : ∀ i j, (β'.1.map τ) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v := by
      apply GlobalTheory.T.integral_of_character_trivial_on_lattice D ψ v hgood n
      intro X hX
      obtain ⟨x, hinf', hoff', htx, hint'⟩ := GlobalTheory.T.exists_global_hermitian_local_approximation D n v τ X
      rw [← htx, ← GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ x hinf' hoff' β']
      apply hint
      unfold PositivityTheory.Rg.Rsw.L.IntAt
      exact ⟨hinf', hoff', hint' hX⟩
    let T₀ : Matrix (Fin n) (Fin n) (Ov D v) := fun i j => ⟨(β'.1.map τ) i j, hTint i j⟩
    have hT : (β'.1.map τ : Matrix (Fin n) (Fin n) (Lv D v)) = T₀.map (algebraMap (Ov D v) (Lv D v)) := rfl
    have hne : T₀.map (IsLocalRing.residue (Ov D v)) ≠
        Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0 := by
      intro heq
      have h1 := GlobalTheory.T.rank_residue_le_rank_generic (Ov D v) (Lv D v) n T₀
      have h2 := GlobalTheory.Core.Rk.rank_map_field (τ : D.host.E →+* Fv D.host.F v) β'.1
      rw [heq, hβ] at h1
      have h3 : (T₀.map (algebraMap (Ov D v) (Lv D v))).rank = (β'.1.map τ).rank := by rw [← hT]
      exact absurd (h1.trans (h3.trans h2).le) (not_le.2 hβ')
    have hpch : ∀ Y, PositivityTheory.Rg.Rsw.L.pch ψ (f Y).1 (GlobalTheory.MixModel.rat β'.1) =
        ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
      intro Y
      rw [GlobalTheory.T.character_pairing_local_hermitian D n v τ ψ (f Y) (hinf Y) (hoff Y) β', hfX Y, hT]
      exact psiV_lift D ψ v w ψ₀ hψ₀c ℓ hℓ Y T₀
    show ∑ x ∈ Finset.univ.image f, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0)
      (Function.invFun f x) * PositivityTheory.Rg.Rsw.L.pch ψ x.1 (GlobalTheory.MixModel.rat β'.1) = 0
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    calc _ = ∑ Y, coY ψ₀ (Matrix.diagonal fun i : Fin n => if i.1 < r then (1 : kv D v) else 0) Y *
          ψ₀ (Matrix.trace (Y * T₀.map (IsLocalRing.residue (Ov D v)))) := by
            refine Finset.sum_congr rfl fun Y _ => ?_
            rw [Function.leftInverse_invFun hfinj Y, hpch Y]
      _ = 0 := GlobalTheory.T.sum_character_orthogonality_matrices (kv D v) n ψ₀ hψ₀ _ _ hne
  · intro νv hH hP z
    have e1 : ∀ g, GlobalTheory.CompanionTheory.Jp.sphV D n v z g =
        GlobalTheory.Doubling.npow (hU D n v τ (thU D n v τ g)) (z + (n : ℂ) / 2) := by
      intro g
      rw [hU_thU]
      rfl
    rw [← hcint ϖ hϖ w hw ℓ hℓ (nvL D v) hok (hU D n v τ) (hU_isHgt D n v τ) _ νv ρ hρs (hρm ϖ hϖ) z]
    dsimp only
    congr 1
    funext k
    rw [Finset.sum_image (fun Y _ Y' _ h => hfinj h)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Function.leftInverse_invFun hfinj Y, e1, map_mul, map_mul, hρ k, GlobalTheory.T.local_image_of_unipotent_element D n nb hnb v τ (f Y), hfX Y]
    rfl

end GlobalTheory.CompanionTheory.Jp

end
