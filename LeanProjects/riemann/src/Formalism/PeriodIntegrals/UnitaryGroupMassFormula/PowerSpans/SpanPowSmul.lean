import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.ProjCW

open Formalism.BasicNotions NumberField IsDedekindDomain

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem locLe_map (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (M N : Submodule (𝓞 K) V)
    (f : V →ₗ[𝓞 K] V) (h : LocLe w F M N) : LocLe w F (M.map f) (N.map f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨s, hs, hsx⟩ := h x hx
  refine ⟨s, hs, ?_⟩
  rw [← map_smul, ← Submodule.map_smul'']
  exact Submodule.mem_map_of_mem hsx

theorem span_map_eq (φ : V →ₗ[K] V) (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K ((M.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
      LinearMap.range φ := by
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hM, Submodule.map_top]

theorem span_pow_smul (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (N : Submodule (𝓞 K) V) :
    Submodule.span K ((((w.asIdeal ^ F) • N : Submodule (𝓞 K) V)) : Set V) =
      Submodule.span K (N : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right (I := w.asIdeal ^ F) (N := N))
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hbF : b ^ F ∈ w.asIdeal ^ F := Ideal.pow_mem_pow hb F
    have hbF0 : (algebraMap (𝓞 K) K (b ^ F)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact pow_ne_zero F hb0
    rw [Submodule.span_le]
    intro n hn
    have h1 : (b ^ F) • n ∈ ((w.asIdeal ^ F) • N : Submodule (𝓞 K) V) := Submodule.smul_mem_smul hbF hn
    have h2 : n = (algebraMap (𝓞 K) K (b ^ F))⁻¹ • ((algebraMap (𝓞 K) K (b ^ F)) • n) := by
      rw [smul_smul, inv_mul_cancel₀ hbF0, one_smul]
    rw [SetLike.mem_coe, h2, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem ker_one_sub (e : Module.End K V) (he : e * e = e) :
    LinearMap.ker (1 - e) = LinearMap.range e := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact ⟨x, hx.symm⟩
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, ← Module.End.mul_apply, he, sub_self]

end General

theorem projC_of (hI : PI.Dv.IdxCalc) : PI.Dv.ProjC := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, -, he, -, -⟩ := hP
  obtain ⟨-, hAfg, hAsp⟩ := hG
  intro Th hTh
  obtain ⟨hTfg, hTsp⟩ := hTh
  have hker : LinearMap.ker (1 - e) = LinearMap.range e := ker_one_sub e he
  have hsp : Submodule.span K (A.L : Set A.V) = Submodule.span K (Th : Set A.V) := by rw [hAsp, hTsp]
  set φ : A.V →ₗ[𝓞 K] A.V := (1 - e : Module.End K A.V).restrictScalars (𝓞 K) with hφ
  set φA := A.L.map φ with hφA
  set φT := Th.map φ with hφT
  have fgA : φA.FG := hAfg.map φ
  have fgT : φT.FG := hTfg.map φ
  have spA : Submodule.span K (φA : Set A.V) = LinearMap.range (1 - e) := span_map_eq (1 - e) A.L hAsp
  have spT : Submodule.span K (φT : Set A.V) = LinearMap.range (1 - e) := span_map_eq (1 - e) Th hTsp
  have rkA : Formalism.HN.rkK φA = dimE A (1 - e) := by
    unfold Formalism.HN.rkK dimE; rw [spA]
  have rkT : Formalism.HN.rkK φT = dimE A (1 - e) := by
    unfold Formalism.HN.rkK dimE; rw [spT]
  have hex : ∀ w, idxAt w A.L Th = idxAt w (cutE A e A.L) (cutE A e Th) + idxAt w φA φT := by
    intro w
    have h3 := (hI K A.V w A.L Th hAfg hTfg hsp).2.2.1 A.V (1 - e)
    rw [hker] at h3
    exact h3
  refine ⟨?_, ?_, ?_⟩
  · intro w F hL
    have h4 := (hI K A.V w φA φT fgA fgT (spA.trans spT.symm)).2.2.2.1 F (locLe_map w F Th A.L φ hL)
    rw [rkA] at h4
    have := hex w
    linarith
  · intro w F hL
    set P : Submodule (𝓞 K) A.V := (w.asIdeal ^ F) • φT with hPdef
    have fgP : P.FG := Submodule.FG.of_le fgT Submodule.smul_le_right
    have spP : Submodule.span K (P : Set A.V) = LinearMap.range (1 - e) := by
      rw [hPdef, span_pow_smul, spT]
    have hLP : LocLe w 0 P φA := by
      have := locLe_map w 0 ((w.asIdeal ^ F) • Th) A.L φ hL
      rw [Submodule.map_smul''] at this
      exact this
    have h2 := (hI K A.V w φA P fgA fgP (spA.trans spP.symm)).2.1 φT fgT (spT.trans spP.symm)
    have h4 := (hI K A.V w φA P fgA fgP (spA.trans spP.symm)).2.2.2.1 0 hLP
    have h5 := (hI K A.V w φT φT fgT fgT rfl).2.2.2.2.1 F
    rw [rkT] at h5
    have hanti : idxAt w P φT = - idxAt w φT P := by
      unfold idxAt; ring
    have := hex w
    push_cast at h4
    linarith
  · intro x hx
    obtain ⟨hxT, y, hy⟩ := hx
    refine ⟨x, hxT, ?_⟩
    show e x = x
    rw [← hy, ← Module.End.mul_apply, he]

end PI.Dv.ProjCW
