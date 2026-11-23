import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DeRhamSpan

open GlobalTheory.DeRhamCompare
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod)

theorem span_of_invariant {G E M : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Module.Finite E M] {n : ℕ} (hn : n = finrank E M)
    (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : Fin n → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : Fin n → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (y : M) : ∃ c : Fin n → E, ∑ i, c i • v i = y := by
  letI := hE.toField
  have h := GlobalTheory.Per.linearIndependent_of_invariant G E M (Fin n) σ ρ hρ v hv hind
  have h2 := h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; exact hn)
  exact (Submodule.mem_span_range_iff_exists_fun E).1 (h2 ▸ Submodule.mem_top)

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_DdRK [FiniteDimensional Qp LL] [FiniteDimensional LL V] (h : IsDR PD ρ) :
    FiniteDimensional K (DdRK PD ρ) ∧ finrank K (DdRK PD ρ) = finrank Qp V := by
  have := PD.finK
  have := finite_DdR PD ρ h
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (DdR PD ρ) := Module.Finite.trans LL _
  let ε : DdR PD ρ ≃ₗ[Qp] DdRK PD ρ :=
    { toFun := fun x => toK PD ρ x x.2
      invFun := fun y => ⟨(TensorProduct.comm Qp V BdR).symm y, y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [toK])
      map_smul' := fun a x => Subtype.ext (by simp [toK])
      left_inv := fun x => Subtype.ext (by simp [toK])
      right_inv := fun x => Subtype.ext (by simp [toK]) }
  have : FiniteDimensional Qp (DdRK PD ρ) := ε.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K (DdRK PD ρ)
  have h2 := Module.finrank_mul_finrank Qp LL (DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  rw [← ε.finrank_eq, ← h2, h, mul_left_comm, h3] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem span_of_isField [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hF : IsField BdR)
    (h : IsDR PD ρ) (y : V ⊗[Qp] BdR) :
    ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR), (∀ i, d i ∈ DdR PD ρ) ∧
      y = ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) := by
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have := hF.nontrivial
  obtain ⟨_, hr⟩ := finrank_DdRK PD ρ h
  let e := Module.finBasisOfFinrankEq K _ hr
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨b, hb⟩ := span_of_invariant (M := BdR ⊗[Qp] V) hF (n := finrank Qp V)
    Module.finrank_baseChange.symm
    (fun g => (PD.actdR g : BdR →+* BdR)) (fun g => (σ g).toAddMonoidHom) hσ
    (fun k => (e k : BdR ⊗[Qp] V))
    (fun g k => by
      have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
      rw [(mem_DdR PD ρ _).1 (e k).2 g, LinearEquiv.apply_symm_apply] at h1
      exact h1)
    (fun c hcg hsum k => by
      choose a ha using fun p => PD.invdR (c p) fun g => hcg g p
      have h1 : ∑ i, a i • e i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, ← ha, algebraMap_smul]
      rw [← ha, Fintype.linearIndependent_iff.1 e.linearIndependent a h1 k, map_zero])
    (TensorProduct.comm Qp V BdR y)
  refine ⟨_, b, fun k => (TensorProduct.comm Qp V BdR).symm (e k), fun k => (e k).2, ?_⟩
  apply (TensorProduct.comm Qp V BdR).injective
  simp only [map_sum, comm_mp, LinearEquiv.apply_symm_apply, hb]

end General

theorem tied_deRham_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ h y
  haveI := LL.2
  exact span_of_isField (P.PD K) ρ (GlobalTheory.Per.TiedField.tied_field l P AI T).1 h y

end GlobalTheory.Per.DeRhamSpan
