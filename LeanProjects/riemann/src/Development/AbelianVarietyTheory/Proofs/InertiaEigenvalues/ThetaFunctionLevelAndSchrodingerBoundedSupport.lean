import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.SupportBound

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_pow_le {v : FinPl D} {ϖ : OI v} (hϖ : Irreducible ϖ) {c d : Fv D.host.F v} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v c ∧
      Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v d := by
  have h1 : Valued.v (algebraMap (OI v) (Fv D.host.F v) ϖ) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have h2 : min (Valued.v c) (Valued.v d) ≠ 0 := by
    rcases min_choice (Valued.v c) (Valued.v d) with h | h <;> rw [h]
    · exact (Valuation.ne_zero_iff _).2 hc
    · exact (Valuation.ne_zero_iff _).2 hd
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 _ h2)
  refine ⟨N, ?_, ?_⟩ <;> rw [map_pow, map_pow]
  · exact hN.le.trans (min_le_left _ _)
  · exact hN.le.trans (min_le_right _ _)

theorem rdQ_ne_zero {v : FinPl D} (φ : SplitProj D v) {x : D.host.E} (hx : x ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x ≠ 0 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x⁻¹ = 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hx]
    exact map_one φ
  exact left_ne_zero_of_mul_eq_one h

theorem map_nsmul_of_add {A B : Type} [AddGroup A] [AddGroup B] {κ : A → B} (h : ∀ x y, κ (x + y) = κ x + κ y) (k : ℕ)
    (x : A) : κ (k • x) = k • κ x :=
  map_nsmul (AddMonoidHom.mk' κ h) k x

theorem symplO_nsmul (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [← Nat.cast_smul_eq_nsmul (AE D), symplO_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem level_and_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ f hf
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨-, a, -, ha0, -, himg⟩ := GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨hadd, hbij, -⟩, -⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1.1
  have he' := isSplitIdem_conj he.1
  have hb := rdQ_ne_zero φ (star_ne_zero.2 ha0)
  generalize GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = b at hb himg
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hkv : Valued.v (k : Fv D.host.F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hk0
  obtain ⟨N, hN1, hN2⟩ := exists_pow_le hϖ (mul_ne_zero hk0 hb) (mul_ne_zero hk0 (inv_ne_zero hb))
  refine ⟨N, fun z hz => ?_, fun ℓ hℓ x hx hne i j => ?_⟩
  · have hy : (k : Fv D.host.F v)⁻¹ • adjCo φ S T (frCo φ βS) (frCo φ βT) z ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      intro i j
      obtain ⟨o, ho⟩ := hz.2 i j
      rw [Matrix.smul_apply, ho, smul_eq_mul, map_mul, map_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hkv),
        ← Valuation.map_mul _ (k : Fv D.host.F v)]
      exact (mul_le_of_le_one_right' o.2).trans hN1
    rw [← himg] at hy
    obtain ⟨t, ⟨ht, hth⟩, hty⟩ := hy
    have : z = k • t := by
      refine hbij.injOn hz.1 (isHalf_nsmul hth k) ?_
      rw [map_nsmul_of_add hadd, hty, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact hUf z (this ▸ hkU t ht) (half_fin he' hz.1)
  · have hkx : k • x ∈ Λ := by
      by_contra hn
      obtain ⟨l, hl, hlh, hl1⟩ := exists_dual_half he' hd (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst)
        (isHalf_nsmul hx k) hn
      rw [GlobalTheory.DualPairCheck.cA_cA] at hlh
      have hlk := isHalf_nsmul hlh k
      have h2 := hℓ _ hlk _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hf)
      rw [heisO_comm, hUf _ (hkU l hl) (half_fin he.1 hlk), map_smul, smul_eq_mul, symplO_nsmul] at h2
      exact hl1 (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
    have hy : adjCo φ S T (frCo φ βS) (frCo φ βT) (k • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      rw [← himg]
      exact ⟨_, ⟨hkx, isHalf_nsmul hx k⟩, rfl⟩
    have h3 := hy i j
    rw [map_nsmul_of_add hadd, Matrix.smul_apply, nsmul_eq_mul] at h3
    refine ⟨⟨algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * adjCo φ S T (frCo φ βS) (frCo φ βT) x i j, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul]
    refine (mul_le_mul_left hN2 _).trans ?_
    rw [← Valuation.map_mul, mul_right_comm, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ h3 zero_le'

end GlobalTheory.DownLift.GenSplit.SupportBound

end
