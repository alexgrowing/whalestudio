import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFMapSubtype
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Transport

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def resF (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (fun x x' y => by simp) (fun c x y => by simp) (fun x y y' => by simp) (fun c x y => by simp)

@[simp] theorem resF_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (x y : W) :
    resF h W x y = h x y := rfl

abbrev incO (W : Submodule K V) : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)

abbrev latW (W : Submodule K V) (T : Submodule (𝓞 K) V) : Submodule (𝓞 K) W := T.comap (incO W)

theorem map_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    (latW W T).map (incO W) = T := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  exact ⟨⟨x, hT.2 ▸ Submodule.subset_span hx⟩, rfl⟩

theorem incO_injective (W : Submodule K V) : Function.Injective (incO W) := Subtype.val_injective

theorem isLattice_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    Submodule.IsLattice K (latW W T) := by
  refine ⟨Submodule.fg_of_fg_map_injective _ (incO_injective W) (by rw [map_latW hT]; exact hT.1), ?_⟩
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
  have himg : (Subtype.val '' ((latW W T : Submodule (𝓞 K) W) : Set W)) = (T : Set V) := by
    have e := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) (map_latW hT)
    simpa [Submodule.map_coe] using e
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Submodule.coe_subtype, himg, hT.2]

private lemma mem_of_algebraMap_smul_mem (W : Submodule K V) {t : 𝓞 F} (ht : t ≠ 0) {x : V}
    (h : algebraMap (𝓞 F) (𝓞 K) t • x ∈ W) : x ∈ W := by
  have hs : algebraMap (𝓞 F) (𝓞 K) t ≠ 0 := fun h0 =>
    ht (NumberField.RingOfIntegers.algebraMap.injective F K (h0.trans (map_zero _).symm))
  have hsK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact_mod_cast hs
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x] at h
  have h2 := W.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hsK, one_smul] at h2

private lemma map_incO_locF (W : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (A : Submodule (𝓞 K) W) : (locF 𝔭 A).map (incO W) = locF 𝔭 (A.map (incO W)) := by
  ext x
  simp only [Submodule.mem_map, Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
  constructor
  · rintro ⟨y, ⟨t, ht, hy⟩, rfl⟩
    exact ⟨t, ht, _, hy, by simp⟩
  · rintro ⟨t, ht, z, hz, hzx⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hxW : x ∈ W := by
      apply mem_of_algebraMap_smul_mem W ht0
      rw [← hzx]
      exact z.2
    refine ⟨⟨x, hxW⟩, ⟨t, ht, ?_⟩, rfl⟩
    convert hz using 1
    exact Subtype.ext hzx.symm

theorem locF_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) (𝔭 : Ideal (𝓞 F))
    [𝔭.IsPrime] : (locF 𝔭 (latW W T)).map (incO W) = locF 𝔭 T := by
  rw [map_incO_locF, map_latW hT]

theorem isJordanIn_res {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {T : Submodule (𝓞 K) V}
    (hT : IsLatIn W T) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {b : Fin (finrank K W) → V} {a : Fin (finrank K W) → 𝓞 F}
    (hb : IsJordanIn h W T 𝔭 b a) :
    IsJordanIn (resF h W) ⊤ (latW W T) 𝔭
      (fun i => ⟨b (finCongr (finrank_top K W) i), hb.1 _⟩) (fun i => a (finCongr (finrank_top K W) i)) := by
  obtain ⟨hbW, hloc, horth, hdiag, hne⟩ := hb
  refine ⟨fun i => Submodule.mem_top, ?_, ?_, ?_, fun i => hne _⟩
  · apply Submodule.map_injective_of_injective (incO_injective W)
    have himg : ⇑(incO W) '' Set.range (fun i : Fin (finrank K (⊤ : Submodule K W)) =>
        (⟨b (finCongr (finrank_top K W) i), hbW _⟩ : W)) = Set.range b := by
      ext v
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨(finCongr (finrank_top K W)).symm i, rfl⟩, by simp⟩
    rw [map_incO_locF, locF_latW hT, Submodule.map_span, himg, hloc]
  · intro i j hij
    simp only [resF_apply]
    exact horth _ _ ((finCongr (finrank_top K W)).injective.ne hij)
  · intro i
    simp only [resF_apply]
    exact hdiag _

end Transport

end Formalism.L2.SG.Pf.G8
