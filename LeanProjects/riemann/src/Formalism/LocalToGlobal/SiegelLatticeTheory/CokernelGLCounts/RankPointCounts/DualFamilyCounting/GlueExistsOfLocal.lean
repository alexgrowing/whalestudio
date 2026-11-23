import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfOf
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zmult_of_span (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hnx m
    · rw [mul_smul]; exact zsmul_mem hmy n
  | smul a x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, α, hα⟩ := Formalism.HermitianLatticesTheory.traceReal_den a
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : (k * n) • (a • x) = α • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul K (k * n), ← algebraMap_smul K α (n • x),
        ← Int.cast_smul_eq_zsmul K n, smul_smul, smul_smul]
      congr 1
      rw [show algebraMap (NumberField.RingOfIntegers K) K α = (α : K) from rfl, ← hα]
      push_cast
      ring
    rw [e1]
    exact M.smul_mem α hnx

def zdiv (B : Submodule (𝓞 K) V) (n : ℤ) : Submodule (𝓞 K) V where
  carrier := {x | n • x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show n • (a + b) ∈ B
    rw [smul_add]
    exact B.add_mem ha hb
  smul_mem' := by
    intro c x hx
    show n • (c • x) ∈ B
    rw [smul_comm]
    exact B.smul_mem c hx

theorem exists_zsmul_of_fg {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ y ∈ A, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! m hm hmy using fun y (hy : y ∈ S) => hAB y (Submodule.subset_span hy)
  refine ⟨∏ y ∈ S, m y, Finset.prod_ne_zero_iff.2 hm, fun x hx => ?_⟩
  show x ∈ zdiv B (∏ y ∈ S, m y)
  refine (Submodule.span_le.2 ?_) hx
  intro y hy
  show (∏ y ∈ S, m y) • y ∈ B
  rw [← Finset.prod_erase_mul S m hy, mul_smul]
  exact zsmul_mem (hmy y hy) _

theorem locF_le_of_zsmul {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx

theorem badFinite : BadFinite := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF Λ₀ hΛ₀ U M hM
  classical
  set N : Submodule (𝓞 K) V := Λ₀ ⊓ U.restrictScalars (𝓞 K) with hN
  have hMU : ∀ y ∈ M, y ∈ U := fun y hy => by
    rw [← hM.2]; exact Submodule.subset_span hy
  obtain ⟨n₁, hn₁, h₁⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ M, n • x ∈ N := by
    refine exists_zsmul_of_fg hM.1 fun y hy => ?_
    obtain ⟨m, hm, hmy⟩ := Formalism.HermitianLatticesTheory.traceReal_mult Λ₀ hΛ₀ y
    exact ⟨m, hm, Submodule.mem_inf.2 ⟨hmy, zsmul_mem (hMU y hy) m⟩⟩
  have hNfg : N.FG := Submodule.FG.of_le hΛ₀.fg inf_le_left
  obtain ⟨n₂, hn₂, h₂⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ N, n • x ∈ M := by
    refine exists_zsmul_of_fg hNfg fun y hy => zmult_of_span M y ?_
    rw [hM.2]
    exact (Submodule.mem_inf.1 hy).2
  set a : 𝓞 F := ((n₁ * n₂ : ℤ) : 𝓞 F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Int.cast_ne_zero]
    exact mul_ne_zero hn₁ hn₂
  have hD : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | a ∈ 𝔭.1}.Finite := by
    refine ((Ideal.finite_factors hD).image (fun v =>
      (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
    intro 𝔭 h𝔭
    have hne : 𝔭.1 ≠ ⊥ := fun e => ha0 (by
      have : a ∈ 𝔭.1 := h𝔭
      rwa [e, Ideal.mem_bot] at this)
    refine ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, ?_, rfl⟩
    show 𝔭.1 ∣ Ideal.span {a}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
  have haP : a ∉ 𝔭.1 := fun h => h𝔭 (hfin.mem_toFinset.2 h)
  have e : a = (n₁ : 𝓞 F) * (n₂ : 𝓞 F) := by rw [ha]; push_cast; ring
  have h1P : (n₁ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_right _ _ h)
  have h2P : (n₂ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_left _ _ h)
  exact le_antisymm (locF_le_of_zsmul 𝔭.2.isPrime n₂ h2P h₂)
    (locF_le_of_zsmul 𝔭.2.isPrime n₁ h1P h₁)

theorem glueExists_of_local (hloc : GlueLocal) : GlueExists :=
  glueExists_of_of hloc badFinite

end Formalism.L2.SG.Pf.G7
