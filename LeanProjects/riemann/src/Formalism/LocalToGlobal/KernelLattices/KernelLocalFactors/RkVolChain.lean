import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Imports
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantOfTrianglesData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.OneEntryMem
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PullMulRight
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNormOne
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemStandardThetaLatticeIffAdelicIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.FinrankRow
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuConc
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ReductionOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLComm
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PolFamInhabited
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Family
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndepOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HermitianPairingIntegral
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopNorm
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsometryLinkageTrivialLevel
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsometryLinkageAtSplitPrime
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkChi
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.Cd.KS

open Formalism.L2.Ker.KS hiding La_left La_nsmul La_right YYl_nsmul al_flat alpha_flat fixed_pb fnPow_eq form_flat hPow_hOne herm_pb homL_nsmul inter_pb lamM' latPow_eq locNorm_ambOf_of locNorm_thF_of not_dvd_relIdx opU_pb pb relIdx_pb reps_pb selfDual_pb semi_pb thF_ambOf thM' th_pb

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (Sesq IsHerm IsPosDef altE opU dualLat IsSelfDual IsSemiChar fixedBy sumU IsReps relIdx inter Th IsLat matH alphaQ
  CmOK cosetRepsExist InterReps_of semicharacterHom)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (hSc hPow latPow fnPow LocNormScale LocNormPow LocNormInter)

section Gen

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)

abbrev pb (Λ : AddSubgroup W) : AddSubgroup V := Λ.comap e.toLinearMap.toAddMonoidHom

theorem relIdx_pb (Λ₁ Λ₂ : AddSubgroup W) : relIdx (pb e Λ₁) (pb e Λ₂) = relIdx Λ₁ Λ₂ := by
  unfold relIdx
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  exact e.surjective

variable (H : Sesq V) (H' : Sesq W) (hH : ∀ x y, H x y = H' (e x) (e y))

include hH

theorem opU_pb (x z : V) (F : W → ℂ) : opU H x (fun v => F (e v)) z = opU H' (e x) F (e z) := by
  simp only [opU, map_add, hH]

theorem herm_pb (h : IsHerm H') : IsHerm H := fun x y => by rw [hH, hH]; exact h _ _

theorem semi_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x))
    (h : IsSemiChar H' Λ α') : IsSemiChar H (pb e Λ) α := by
  refine ⟨fun x hx => by rw [hα x hx]; exact h.1 _ hx, fun x hx y hy => ?_⟩
  have hx' : e x ∈ Λ := hx
  have hy' : e y ∈ Λ := hy
  have hxy : e (x + y) ∈ Λ := by rw [map_add]; exact Λ.add_mem hx' hy'
  rw [hα _ hxy, hα x hx', hα y hy', map_add, h.2 _ hx' _ hy']
  simp only [altE, hH]

theorem fixed_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x)) {F : W → ℂ}
    (h : F ∈ fixedBy H' α' Λ) : (fun v => F (e v)) ∈ fixedBy H α (pb e Λ) := by
  intro x hx z
  have hx' : e x ∈ Λ := hx
  rw [opU_pb e H H' hH, hα x hx']
  exact h _ hx' _

theorem selfDual_pb {Λ : AddSubgroup W} (h : IsSelfDual H' Λ) : IsSelfDual H (pb e Λ) := by
  unfold IsSelfDual at h ⊢
  ext x
  constructor
  · intro hx
    show e x ∈ Λ
    rw [← h]
    intro y' hy'
    obtain ⟨m, hm⟩ := hx (e.symm y') (show e (e.symm y') ∈ Λ by simpa using hy')
    refine ⟨m, ?_⟩
    simpa [altE, hH] using hm
  · intro hx
    have hx' : e x ∈ dualLat H' Λ := by
      rw [h]
      exact hx
    intro y hy
    obtain ⟨m, hm⟩ := hx' (e y) hy
    refine ⟨m, ?_⟩
    simpa [altE, hH] using hm

theorem reps_pb {Λ₁ Λ₂ : AddSubgroup W} {S : Finset W} (hS : IsReps Λ₁ Λ₂ S) :
    IsReps (pb e Λ₁) (pb e Λ₂) (S.map e.symm.toEquiv.toEmbedding) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    show e (e.symm y) ∈ Λ₂
    rw [e.apply_symm_apply]
    exact hS.1 y hy
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    have : e (e.symm x' - e.symm y') ∈ Λ₁ := hxy
    rw [map_sub, e.apply_symm_apply, e.apply_symm_apply] at this
    rw [hS.2.1 x' hx' y' hy' this]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hS.2.2 (e y) hy
    refine ⟨e.symm x, Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    show e (y - e.symm x) ∈ Λ₁
    rwa [map_sub, e.apply_symm_apply]

theorem inter_pb (hH' : IsHerm H') (Λ₁ Λ₂ : AddSubgroup W) (α : V → ℂ) (α' : W → ℂ)
    (hα₁ : ∀ x, e x ∈ Λ₁ → α x = α' (e x)) (hα₂ : ∀ x, e x ∈ Λ₂ → α x = α' (e x))
    (hS : IsSemiChar H' Λ₂ α') (hidx : relIdx Λ₁ Λ₂ ≠ 0) (F : W → ℂ) (hF : F ∈ fixedBy H' α' Λ₁) :
    inter H α (pb e Λ₁) (pb e Λ₂) (fun v => F (e v)) = fun z => inter H' α' Λ₁ Λ₂ F (e z) := by
  funext z
  obtain ⟨⟨S, hSr⟩, -⟩ := cosetRepsExist W Λ₁ Λ₂ hidx
  rw [InterReps_of semicharacterHom W H' hH' Λ₁ Λ₂ α' hS F hF S hSr (e z),
    InterReps_of semicharacterHom V H (herm_pb e H H' hH hH') _ _ α (semi_pb e H H' hH hα₂ hS) _
      (fixed_pb e H H' hH hα₁ hF) _ (reps_pb e H H' hH hSr) z, relIdx_pb]
  congr 1
  simp only [sumU, Finset.sum_map]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : e (e.symm x) ∈ Λ₂ := by rw [e.apply_symm_apply]; exact hSr.1 x hx
  show α (e.symm x) * opU H (e.symm x) (fun v => F (e v)) z = _
  rw [opU_pb e H H' hH, hα₂ _ hx2, e.apply_symm_apply]

end Gen

section GenTh

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  (e : V ≃ₗ[ℂ] W) (H : Sesq V) (H' : Sesq W) (hH : ∀ x y, H x y = H' (e x) (e y))

include hH in
theorem th_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x)) {F : W → ℂ}
    (h : F ∈ Th H' α' Λ) : (fun v => F (e v)) ∈ Th H α (pb e Λ) := by
  refine ⟨?_, fixed_pb e H H' hH hα h.2⟩
  have h1 : AnalyticOnNhd ℂ (LinearMap.toContinuousLinearMap e.toLinearMap) Set.univ :=
    (LinearMap.toContinuousLinearMap e.toLinearMap).analyticOnNhd _
  exact h.1.comp h1 (fun _ _ => Set.mem_univ _)

end GenTh

theorem not_dvd_relIdx {V : Type*} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) (p s : ℕ) [Fact p.Prime] (hs : Nat.Coprime s p)
    (h0 : relIdx Λ₁ Λ₂ ≠ 0) (hk : ∀ x ∈ Λ₂, s • x ∈ Λ₁) : ¬ p ∣ relIdx Λ₁ Λ₂ := by
  intro hd
  have h0' : Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≠ 0 := h0
  have hd' : p ∣ Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := hd
  have : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero h0'
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' p hd'
  have hsq : s • q = 0 := by
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul]
    exact hk _ a.2
  have h1 : p ∣ s := hq ▸ addOrderOf_dvd_of_nsmul_eq_zero hsq
  have h2 : p ∣ Nat.gcd s p := Nat.dvd_gcd h1 dvd_rfl
  rw [hs] at h2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h2)

section LaS

variable {D : Car} {N N' : ℕ}

theorem homL_nsmul (s : ℕ) {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L₂, A.mulVec x ∈ L₂') → ∀ x ∈ L₁, (s • A).mulVec x ∈ L₁')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.homL D L₂ L₂') : s • A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.homL D L₁ L₁' := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact Submodule.subset_span (h A hA)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A A' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul r A _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1

theorem YYl_nsmul (s : ℕ) {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L₂, A.mulVec x ∈ L₂') → ∀ x ∈ L₁, (s • A).mulVec x ∈ L₁')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.YYl D L₂ L₂') : s • A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.YYl D L₁ L₁' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, A', hA', rfl⟩ := hA
    exact Submodule.subset_span ⟨a, ha, s • A', homL_nsmul s h hA', smul_comm _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A A' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul r A _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ _ h1

theorem La_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (s : ℕ) {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L₂, A.mulVec x ∈ L₂') → ∀ x ∈ L₁, (s • A).mulVec x ∈ L₁')
    {z : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D N N'} (hz : z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L₂ L₂') : s • z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w, hw, s • A, YYl_nsmul s h hA, ?_⟩
    rw [smul_comm]
    congr 1
    funext τ i j
    show s • Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (A i j) = Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s • A i j)
    rw [map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [smul_neg]; exact neg_mem h1

theorem La_left (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (s : ℕ) {L₁ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : ∀ x ∈ L₁, (s : D.host.E) • x ∈ L)
    {z : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D N N'} (hz : z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L L') : s • z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L₁ L' := by
  refine La_nsmul cc δ s (fun A hA x hx => ?_) hz
  have h1 := hA _ (h x hx)
  rw [Matrix.mulVec_smul, Nat.cast_smul_eq_nsmul] at h1
  rwa [Matrix.smul_mulVec]

theorem La_right (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (s : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    {L₁' L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : ∀ x ∈ L', (s : D.host.E) • x ∈ L₁')
    {z : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D N N'} (hz : z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L L') : s • z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L L₁' := by
  refine La_nsmul cc δ s (fun A hA x hx => ?_) hz
  have h1 := h _ (hA x hx)
  rw [Nat.cast_smul_eq_nsmul] at h1
  rwa [Matrix.smul_mulVec]

end LaS

section Flat

variable {D : Car} {X : Fields} (s : Seam D X) {a b : ℕ}

theorem form_flat (A : ℝ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b A⁻¹) x y = formV A D.what₂.Tau a b (s.flatV a b x) (s.flatV a b y) := by
  rw [formV_apply]
  show (∑ i, ∑ j, x i * hSc X.Tau a b A⁻¹ i j * conj (y j)) = _
  simp only [hSc, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp s.iT.symm, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  show x (s.iT.symm τ, i, j) * ((A⁻¹ : ℝ) : ℂ) * conj (y (s.iT.symm τ, i, j)) =
    x (s.iT.symm τ, i, j) * conj (y (s.iT.symm τ, i, j)) / (A : ℂ)
  rw [Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem alpha_flat (c A : ℝ) (x : DVar X.Tau a b → ℂ) :
    alphaQ c (matH (hSc X.Tau a b A⁻¹)) x = alphaQ c (formV A D.what₂.Tau a b) (s.flatV a b x) := by
  simp only [alphaQ, Formalism.L2.Th1.H.qOf, form_flat s]

theorem hPow_hOne (L : PeriodPair) :
    hPow (Fin b × Fin a) (hOne L X.Tau) = hSc X.Tau a b (Formalism.L2.Th1.F.area L)⁻¹ := by
  ext w w'
  simp only [hPow, hOne, hSc, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h1 : w = w'
  · subst h1
    simp
  · rw [if_neg h1]
    by_cases h2 : w.2 = w'.2
    · have h3 : w.1 ≠ w'.1 := fun h => h1 (Prod.ext h h2)
      simp [h2, h3]
    · simp [h2]

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def lamM' : AddSubgroup (X.Tau → ℂ) :=
  B.lamM.comap (LinearEquiv.funCongrLeft ℂ ℂ s.iT.symm).toLinearMap.toAddMonoidHom

def thM' : (X.Tau → ℂ) → ℂ := fun z => B.thMM fun τ => z (s.iT.symm τ)

theorem al_flat (hQ : B.QIntAll) {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') (x : DVar X.Tau a b → ℂ) (hx : s.flatV a b x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L') :
    alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)) x = Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor (s.flatV a b x) := by
  obtain ⟨m, hm⟩ := hQ a b L L' hA _ hx
  rw [alpha_flat s]
  exact (al_eq D B.tor _ m hm).symm

theorem latPow_eq : latPow (Fin b × Fin a) (lamM' s B) = s.laF B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b) := by
  ext z
  show (∀ i : Fin b × Fin a, (fun τ => z (s.iT.symm τ, i)) ∈ B.lamM) ↔ s.flatV a b z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor _ _
  rw [show Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b) = powLat B.lamM a b from B.lat0OK a b]
  show _ ↔ ∀ i j, (fun τ => z (s.iT.symm τ, i, j)) ∈ B.lamM
  exact Prod.forall

theorem fnPow_eq : fnPow (Fin b × Fin a) (thM' s B) = fun z => B.thZero a b (s.flatV a b z) := by
  funext z
  show ∏ i : Fin b × Fin a, B.thMM (fun τ => z (s.iT.symm τ, i)) = ∏ i : Fin b, ∏ j : Fin a, B.thMM fun τ => z (s.iT.symm τ, i, j)
  rw [Fintype.prod_prod_type]

theorem locNorm_thF_of (hS : LocNormScale) (hP : LocNormPow) (hI : LocNormInter) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hSDM : IsSelfDual (matH (hOne B.L X.Tau)) (lamM' s B))
    (hStM : ∀ x ∈ lamM' s B, Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ lamM' s B)
    (hThM : thM' s B ∈ Th (matH (hOne B.L X.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L X.Tau))) (lamM' s B))
    (hMM : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B.L X.Tau) (lamM' s B) (thM' s B) p ι)
    (hPD : IsPosDef (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
    (hLat : ∀ L L', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L' → IsLat (s.laF B.tor L L'))
    (hSt : ∀ L L', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L' → ∀ x ∈ s.laF B.tor L L', Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L')
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') (hL : Formalism.L2.Ker.Cd.TaylorLogMetric.EqAt D p (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) L) (hL' : Formalism.L2.Ker.Cd.TaylorLogMetric.EqAt D p (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b) L')
    (hχ : ‖ι (Formalism.L2.Ker.Cd.Base.chiFac χ a b L L')‖ ≤ 1) :
    LocNorm a₀ b₀ D.host.d ha hd lam hlam (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L')
      (fun z => B.eNat χ a b L L' (s.flatV a b z)) p ι := by
  have h0 : δ ≠ 0 := Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ
  have hStd := B.stdOK hcc hδ
  have hLA := B.latAll hcc hδ h0
  have hQ : B.QIntAll := Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B
  have hAr : TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have hf := form_flat s (a := a) (b := b) (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))
  have hHerm' := formV_herm (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b
  have hHerm := herm_pb (s.flatV a b) _ _ hf hHerm'
  have A0 := Formalism.L2.Ker.Cd.Base.first_coordinate_admissible hA
  have A1 := Formalism.L2.Ker.Cd.Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA
  have sd : ∀ L L', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L' →
      IsSelfDual (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)) (s.laF B.tor L L') :=
    fun L L' h => selfDual_pb (s.flatV a b) _ _ hf (hLA.1 a b L L' h).1
  have idx : ∀ L₁ L₁' L₂ L₂', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L₁ L₁' → Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L₂ L₂' →
      relIdx (s.laF B.tor L₁ L₁') (s.laF B.tor L₂ L₂') ≠ 0 := by
    intro L₁ L₁' L₂ L₂' h₁ h₂
    show relIdx (pb (s.flatV a b) _) (pb (s.flatV a b) _) ≠ 0
    rw [relIdx_pb]
    exact (hLA.2 a b _ _ _ _ h₁ h₂).1

  have l0 := hP a₀ b₀ c₀ D.host.d ha hd lam hlam hcm X.Tau (hOne B.L X.Tau) (lamM' s B) hSDM hStM _ hThM p ι hMM (Fin b × Fin a)
  rw [hPow_hOne, latPow_eq, fnPow_eq, ← hAr] at l0

  have t0 := th_pb (s.flatV a b) _ _ hf (al_flat s B hQ A0) (B.thZeroMem hStd a b)
  have e1 := inter_pb (s.flatV a b) _ _ hf hHerm' _ _ _ _ (al_flat s B hQ A0) (al_flat s B hQ A1) (hLA.1 a b _ _ A1).2
    (hLA.2 a b _ _ _ _ A0 A1).1 (B.thZero a b) (B.thZeroMem hStd a b).2
  have n1 : ¬ p ∣ relIdx (s.laF B.tor (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D a) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) (s.laF B.tor L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) := by
    obtain ⟨s₁, hs₁, h₁, -⟩ := hL
    show ¬ p ∣ relIdx (pb (s.flatV a b) _) (pb (s.flatV a b) _)
    rw [relIdx_pb]
    exact not_dvd_relIdx _ _ p s₁ hs₁ (hLA.2 a b _ _ _ _ A0 A1).1 fun x hx => La_left cc δ s₁ _ h₁ hx
  have l1 := hI a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (DVar X.Tau a b) _ _ _ hHerm hPD (hLat _ _ A0) (hLat _ _ A1) (sd _ _ A0) (sd _ _ A1)
    (hSt _ _ A0) (hSt _ _ A1) _ t0 p ι (idx _ _ _ _ A0 A1) (idx _ _ _ _ A1 A0) n1 l0
  have l1' : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b))
      (fun z => B.thHalf a b L (s.flatV a b z)) p ι := by
    have := l1
    erw [e1] at this
    exact this

  have t1 := th_pb (s.flatV a b) _ _ hf (al_flat s B hQ A1) (B.thHalf_mem hStd hLA hA)
  have e2 := inter_pb (s.flatV a b) _ _ hf hHerm' _ _ _ _ (al_flat s B hQ A1) (al_flat s B hQ hA) (hLA.1 a b _ _ hA).2
    (hLA.2 a b _ _ _ _ A1 hA).1 (B.thHalf a b L) (B.thHalf_mem hStd hLA hA).2
  have n2 : ¬ p ∣ relIdx (s.laF B.tor L (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D b)) (s.laF B.tor L L') := by
    obtain ⟨s₂, hs₂, -, h₂⟩ := hL'
    show ¬ p ∣ relIdx (pb (s.flatV a b) _) (pb (s.flatV a b) _)
    rw [relIdx_pb]
    exact not_dvd_relIdx _ _ p s₂ hs₂ (hLA.2 a b _ _ _ _ A1 hA).1 fun x hx => La_right cc δ s₂ _ h₂ hx
  have l2 := hI a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (DVar X.Tau a b) _ _ _ hHerm hPD (hLat _ _ A1) (hLat _ _ hA) (sd _ _ A1) (sd _ _ hA)
    (hSt _ _ A1) (hSt _ _ hA) _ t1 p ι (idx _ _ _ _ A1 hA) (idx _ _ _ _ hA A1) n2 l1'
  have l2' : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L')
      (fun z => B.thMoved a b L L' (s.flatV a b z)) p ι := by
    have := l2
    erw [e2] at this
    exact this

  exact hS a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau a b) _ _ _ p ι _ hχ l2'

theorem thF_ambOf (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    Formalism.L2.AlgTh.thF (ambOf s B χ cD) N N' = fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.flatV a b z) := rfl

theorem locNorm_ambOf_of (hT : LamTie) (hS : LocNormScale) (hP : LocNormPow) (hI : LocNormInter) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hSDM : IsSelfDual (matH (hOne B.L X.Tau)) (lamM' s B))
    (hStM : ∀ x ∈ lamM' s B, Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ lamM' s B)
    (hThM : thM' s B ∈ Th (matH (hOne B.L X.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L X.Tau))) (lamM' s B))
    (hMM : LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B.L X.Tau) (lamM' s B) (thM' s B) p ι)
    (hPD : IsPosDef (matH (hSc X.Tau a b (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)))
    (hLat : ∀ L L', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L' → IsLat (s.laF B.tor L L'))
    (hSt : ∀ L L', Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L' → ∀ x ∈ s.laF B.tor L L', Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L')
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) (hN : s.StdAtP p N) (hN' : s.StdAtP p N')
    (hχ : ‖ι ((ambOf s B χ cD : Amb X).chiF a b N N')‖ ≤ 1) :
    LocNorm a₀ b₀ (ambOf s B χ cD : Amb X).d ha hd lam hlam (hSc X.Tau a b (ambOf s B χ cD : Amb X).sc)
      (Formalism.L2.AlgTh.lamF (ambOf s B χ cD) N N') (Formalism.L2.AlgTh.thF (ambOf s B χ cD) N N') p ι := by
  rw [hT D X s cc δ B χ cD a b N N' hok, thF_ambOf]
  exact locNorm_thF_of s B hS hP hI χ a₀ b₀ c₀ ha hd lam hlam p ι hcc hδ hcm hSDM hStM hThM hMM hPD hLat hSt hA hN hN' hχ

end Flat

end Formalism.L2.Ker.Cd.KS
