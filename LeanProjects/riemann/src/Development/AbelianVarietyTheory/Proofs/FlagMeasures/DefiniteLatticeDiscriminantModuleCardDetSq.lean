import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn

namespace GlobalTheory.LoopC.DetCard

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.MainNotions.S

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V]

theorem map_latIn {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : ∀ x ∈ N, x ∈ U) :
    N.toAddSubgroup = (latIn U N).toAddSubgroup.map U.subtype.toAddMonoidHom := by
  ext x
  constructor
  · intro h1
    exact ⟨⟨x, hN x h1⟩, h1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem idxN_latIn {U : Submodule K V} {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ U)
    (hB : ∀ x ∈ B, x ∈ U) : idxN A B = idxN (latIn U A) (latIn U B) := by
  rw [idxN, idxN, map_latIn hA, map_latIn hB, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem isLattice_latIn_span {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : N.FG)
    (hU : Submodule.span K (N : Set V) = U) : Submodule.IsLattice K (latIn U N) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hN (Submodule.map_comap_le _ _)
  · apply Submodule.map_injective_of_injective U.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine Eq.trans ?_ hU
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU ▸ Submodule.subset_span hx⟩, hx, rfl⟩

variable [StarRing K]

theorem latIn_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    latIn U (Lat.dualInH h N) = dual (hRes h U) (latIn U N) := by
  ext x
  constructor
  · rintro ⟨h1, -⟩
    exact (dualBasic_mem_dual _ _ _).2 fun y hy => (dualBasic_mem_dual _ _ _).1 h1 y hy
  · intro hx
    refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, ?_⟩
    · exact (dualBasic_mem_dual _ _ _).1 hx ⟨z, hU ▸ Submodule.subset_span hz⟩ hz
    · change (x : V) ∈ Submodule.span K (N : Set V)
      rw [hU]
      exact x.2

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    idxN (Lat.dualInH h N) N = discN (hRes h U) (latIn U N) := by
  rw [idxN_latIn (U := U) (A := Lat.dualInH h N) (B := N) (fun x hx => hU ▸ (Submodule.mem_inf.1 hx).2) (fun x hx => hU ▸ Submodule.subset_span hx),
    latIn_dualInH h hU, discN]

theorem general [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) :
    1 ≤ idxN (Lat.dualInH h M) M ∧ (idxN (Lat.dualInH h M) M : ℝ) = Lat.latDetH h M ^ 2 ∧
      ∀ P : Submodule (𝓞 K) V, P ≤ M →
        Module.finrank K (Submodule.span K (P : Set V)) = Module.finrank K (Submodule.span K (M : Set V)) →
        1 ≤ idxN M P ∧ Lat.latDetH h P = Lat.latDetH h M * idxN M P := by
  set U := Submodule.span K (M : Set V) with hUdef
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
  have hnU := DetAgree.nondeg_of_pd hpU
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ M → Submodule.span K (N : Set V) = U →
      IsIntLat (hRes h U) (latIn U N) ∧ discN (hRes h U) (latIn U N) ≠ 0 ∧
        Lat.latDetH h N = Real.sqrt (discN (hRes h U) (latIn U N) : ℝ) := by
    intro N hN hU
    have a : IsIntLat (hRes h U) (latIn U N) :=
      ⟨isLattice_latIn_span (hM.of_le hN) hU, fun x hx y hy => hI x (hN hx) y (hN hy)⟩
    have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
    refine ⟨a, n0, ?_⟩
    rw [← idxN_dualInH h hU] at n0 ⊢
    rw [Lat.latDetH, DetAgree.genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hN hy) x (hN hx), Submodule.subset_span hx⟩
  obtain ⟨m1, m2, m3⟩ := key M le_rfl rfl
  refine ⟨?_, ?_, fun P hP hr => ?_⟩
  · rw [idxN_dualInH h hUdef.symm]
    exact Nat.pos_of_ne_zero m2
  · rw [idxN_dualInH h hUdef.symm, m3, Real.sq_sqrt (Nat.cast_nonneg _)]
  · have hU : Submodule.span K (P : Set V) = U :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hP) hr
    obtain ⟨p1, -, p3⟩ := key P hP hU
    obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
    rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
      (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
    refine ⟨Nat.pos_of_ne_zero q1, ?_⟩
    rw [p3, m3, q2, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)]

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  intro D M hM hp hI
  exact general (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hp M hM hI

end GlobalTheory.LoopC.DetCard
