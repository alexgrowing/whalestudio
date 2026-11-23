import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DRDual

open GlobalTheory.DRFil

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def twistRep (χ : G →* LLˣ) (ρ : Representation LL G V) : Representation LL G V where
  toFun g := ((χ g : LLˣ) : LL) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem act_zpow (T : Fˣ) (hT : (T : F) = PD.ι PD.t) (n : ℤ) (g : G) :
    PD.actdR g ((T ^ n : Fˣ) : F) = ((PD.χ g ^ n : Qpˣ) : Qp) • ((T ^ n : Fˣ) : F) := by
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have h1 : Units.map (PD.actdR g : F →* F) T = Units.map (algebraMap Qp F : Qp →* F) (PD.χ g) * T := by
    ext
    have h2 := PD.ι_comm g PD.t
    rw [PD.t_act, hsm, ← hT, Algebra.smul_def] at h2
    exact h2.symm
  have h3 := congrArg (fun x : Fˣ => ((x ^ n : Fˣ) : F)) h1
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
  rw [Algebra.smul_def, ← map_zpow]
  exact h3

theorem twist_unit (ρ ρ' : Representation LL G V) (u : Fˣ) (n : ℤ) (ψ : G → Qpˣ)
    (hu : (u : F) ∈ PD.Fil n) (hu' : ((u⁻¹ : Fˣ) : F) ∈ PD.Fil (-n))
    (ha : ∀ g, PD.actdR g (u : F) = (ψ g : Qp) • (u : F))
    (ha' : ∀ g, PD.actdR g ((u⁻¹ : Fˣ) : F) = (((ψ g)⁻¹ : Qpˣ) : Qp) • ((u⁻¹ : Fˣ) : F))
    (hρ : ∀ g x, (ψ g : Qp) • ρ' g x = ρ g x) :
    (IsDR PD ρ → IsDR PD ρ') ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD ρ' τ (n + a) = multV PD ρ τ a := by
  have hρ' : ∀ g x, (((ψ g)⁻¹ : Qpˣ) : Qp) • ρ g x = ρ' g x := fun g x => by
    rw [← hρ, smul_smul, Units.inv_mul, one_smul]
  let Φ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V u ∘ₗ ext Qp F LinearMap.id
  let Ψ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (u⁻¹ : Fˣ) ∘ₗ ext Qp F LinearMap.id
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ]
  let E : V ⊗[Qp] F ≃ₗ[LL] V ⊗[Qp] F := LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)
  have hD : (DdR PD ρ).map E.toLinearMap = DdR PD ρ' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_DdR PD ρ ρ' LinearMap.id _ _ ha hρ hx
    · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ LinearMap.id _ _ ha' hρ' hy, h1 y⟩
  have hF : ∀ τ a, (FildR PD ρ τ a).map E.toLinearMap = FildR PD ρ' τ (n + a) := by
    intro τ a
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_FildR PD ρ ρ' LinearMap.id _ _ ha hρ τ hu hx
    · have := twist_mem_FildR PD ρ' ρ LinearMap.id _ _ ha' hρ' τ hu' hy
      rw [neg_add_cancel_left] at this
      exact ⟨Ψ y, this, h1 y⟩
  refine ⟨fun h => ?_, fun τ a => ?_⟩
  · rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h]
  · unfold multV
    rw [add_assoc, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

end Generic

theorem twisted_dual_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m j hm hg h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have h₀ : IsDR (P.PD K) ρ₀ := isDR_of_spans T K LL ρ₀
    (spans_dual_of_spans (P.PD K) ρ ρ₀ m (isField_dR T) hβ hβ' (hs.spans _))
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨h1, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  refine ⟨h1 h₀, fun τ a _ => ?_⟩
  obtain ⟨n, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

end GlobalTheory.DRDual
