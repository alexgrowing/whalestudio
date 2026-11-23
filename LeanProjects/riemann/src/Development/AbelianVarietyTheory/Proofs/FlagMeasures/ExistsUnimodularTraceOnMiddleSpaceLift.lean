import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

open Formalism.HermitianLatticeCounting.P

namespace GlobalTheory.DegCnt.WnLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

def pr : V →ₗ[K] V := LinearMap.id - NFGeom.proj N

theorem pr_add (x : V) : pr N x + NFGeom.proj N x = x := by simp [pr]

theorem Wn_perp_Ist {y : V} (hy : y ∈ N.Wn) : ∀ u ∈ N.Ist, H.B y u = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).2

theorem Wn_perp_II {y : V} (hy : y ∈ N.Wn) {x : V} (hx : x ∈ II N.F N.F') : H.B y x = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).1 x (Submodule.mem_sup_left hx.1)

theorem pr_of_Wn {y : V} (hy : y ∈ N.Wn) : pr N y = y := by
  simp [pr, NFGeom.proj_zero N (Wn_perp_Ist N hy)]

theorem pr_II {x : V} (hx : x ∈ II N.F N.F') : pr N x = 0 := by
  simp [pr, NFGeom.proj_II N hx]

theorem pr_mem_Wn {x : V} (hx : x ∈ uPerp N.F N.F') : pr N x ∈ N.Wn :=
  (NFGeom.mem_perp_sup _ _ _).2
    ⟨Submodule.sub_mem _ hx (NFGeom.II_le_uPerp N (NFGeom.proj_mem N x)), NFGeom.sub_proj_perp N x⟩

theorem Wn_le_uPerp : N.Wn ≤ uPerp N.F N.F' := by
  rw [NFGeom.uPerp_eq N]; exact le_sup_left

theorem orthogonal_perp_z {w : V} (hw : w ∈ N.Wt) : H.B w N.F.z = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hw).1 _ (lastVector_mem_jointSpan_left N.F N.F')

theorem zz : H.B N.F.z N.F.z = -N.F.T := N.F.zz

theorem nondeg_Wn [FiniteDimensional K V] (x : V) (hx : x ∈ N.Wn) (h : ∀ y ∈ N.Wn, H.B x y = 0) :
    x = 0 := by
  have hx' := hx
  rw [NFGeom.Wn_eq N, Submodule.mem_sup] at hx'
  obtain ⟨w, hw, u, hu, rfl⟩ := hx'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have hz := h _ (NFGeom.z_mem_Wn N)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, orthogonal_perp_z N hw,
    zz] at hz
  have ht : t = 0 := by
    have := N.F.hT
    simp at hz
    exact hz.resolve_right this
  subst ht
  simp only [zero_smul, add_zero] at h ⊢
  by_contra h0
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hwW : w ∈ N.Wn := by rw [NFGeom.Wn_eq N]; exact Submodule.mem_sup_left hw
  have := NFGeom.Wt_pos N σ hw h0
  rw [h w hwW] at this
  simp at this

theorem z_ne : N.F.z ≠ 0 := fun h => N.F.hT (by
  have := zz N
  rw [h] at this
  simpa using this.symm)

theorem hermFramePair_middleSpace_inf_span_z_eq_bot : N.Wt ⊓ Submodule.span K {N.F.z} = ⊥ :=
  eq_bot_iff.2 fun x hx => (Submodule.mem_bot K).2 <| by
    obtain ⟨hw, hz⟩ := hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h := orthogonal_perp_z N hw
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, zz] at h
    have := N.F.hT
    rcases mul_eq_zero.1 h with h1 | h1
    · simp [h1]
    · exact absurd (neg_eq_zero.1 h1) this

theorem finrank_Wn [FiniteDimensional K V] : Module.finrank K N.Wn + 2 * r = Module.finrank K V := by
  have h1 := NFGeom.finrank_Wt N
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt (Submodule.span K {N.F.z})
  rw [hermFramePair_middleSpace_inf_span_z_eq_bot, finrank_bot, finrank_span_singleton (z_ne N), ← NFGeom.Wn_eq N] at h2
  omega

def hW [FiniteDimensional K V] : HermSpace K N.Wn where
  B := H.B.domRestrict₁₂ N.Wn N.Wn
  herm x y := H.herm x y
  nondeg x hx := Submodule.coe_eq_zero.1 (nondeg_Wn N x x.2 fun y hy => hx ⟨y, hy⟩)

theorem hW_B [FiniteDimensional K V] (x y : N.Wn) : (hW N).B x y = H.B x y := rfl

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt.WnLat

open Formalism.HermitianLatticeCounting.P

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem unimod (L : Submodule (𝓞 K) V) (hL : IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F')) :
    GlobalTheory.HermLat.IsUnimod (hW N) (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  obtain ⟨⟨⟨N0, hN0, hLeq⟩, hspanL⟩, hdL⟩ := hL
  set M := L.comap (N.Wn.subtype.restrictScalars (𝓞 K)) with hM
  have hIL : ∀ x ∈ II N.F N.F', x ∈ L := fun x hx => by
    rw [hLeq]; exact Submodule.mem_sup_right hx
  have hprL : ∀ x ∈ L, pr N x ∈ L := fun x hx => by
    have : pr N x = x - NFGeom.proj N x := by simp [pr]
    rw [this]; exact L.sub_mem hx (hIL _ (NFGeom.proj_mem N x))
  have hprW : ∀ x ∈ L, pr N x ∈ N.Wn := fun x hx => by
    refine pr_mem_Wn N ?_
    rw [← hspanL]; exact Submodule.subset_span hx
  have hS : L ⊓ rs (𝓞 K) N.Wn = N0.map ((pr N).restrictScalars (𝓞 K)) := by
    apply le_antisymm
    · rintro x ⟨hxL, hxW⟩
      have hxL' := hxL
      rw [hLeq] at hxL'
      obtain ⟨n, hn, i, hi, rfl⟩ := Submodule.mem_sup.1 hxL'
      refine ⟨n, hn, ?_⟩
      show pr N n = n + i
      have h1 : pr N (n + i) = n + i := pr_of_Wn N hxW
      rwa [map_add, pr_II N hi, add_zero] at h1
    · rintro _ ⟨n, hn, rfl⟩
      have hnL : n ∈ L := by rw [hLeq]; exact Submodule.mem_sup_left hn
      exact ⟨hprL n hnL, hprW n hnL⟩
  have hmap : M.map (N.Wn.subtype.restrictScalars (𝓞 K)) = L ⊓ rs (𝓞 K) N.Wn := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
    · rintro ⟨hxL, hxW⟩; exact ⟨⟨x, hxW⟩, hxL, rfl⟩
  have hfg : M.FG := by
    refine Submodule.fg_of_fg_map_injective (N.Wn.subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    rw [hmap, hS]; exact hN0.map _
  have hspan : Submodule.span K (M : Set N.Wn) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := N.Wn.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_subtype_top]
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨y, _, rfl⟩; exact y.2
    · intro w hw
      have h1 : w ∈ Submodule.span K (L : Set V) := by rw [hspanL]; exact Wn_le_uPerp N hw
      have h2 : pr N w ∈ (Submodule.span K (L : Set V)).map (pr N) := Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, pr_of_Wn N hw] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨pr N x, hprW x hx⟩, hprL x hx, rfl⟩
  have hdual : dual (hW N) M = M := by
    ext y
    rw [mem_dual_iff, hspan]
    simp only [Submodule.mem_top, true_and]
    constructor
    · intro h
      show (y : V) ∈ L
      rw [← hdL, mem_dual_iff, hspanL]
      refine ⟨Wn_le_uPerp N y.2, fun x hx => ?_⟩
      have h1 := h ⟨pr N x, hprW x hx⟩ (hprL x hx)
      rw [hW_B] at h1
      rw [← pr_add N x, map_add, Wn_perp_II N y.2 (NFGeom.proj_mem N x), add_zero]
      exact h1
    · intro hy x hx
      rw [hW_B]
      have : (y : V) ∈ dual H L := by rw [hdL]; exact hy
      exact ((mem_dual_iff H L y).1 this).2 x hx
  exact ⟨⟨⟨M, hfg, by simp [rs]⟩, hspan⟩, hdual⟩

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt

theorem NF.wnUnimod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hL
  exact ⟨WnLat.hW N, WnLat.hW_B N, WnLat.finrank_Wn N, WnLat.unimod N L hL⟩

end GlobalTheory.DegCnt
