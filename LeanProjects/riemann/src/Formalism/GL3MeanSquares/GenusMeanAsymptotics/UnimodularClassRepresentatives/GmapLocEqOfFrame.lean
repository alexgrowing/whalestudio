import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnimodularOfMemGenusOrtho
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

theorem gmap_loc_eq_of_frame {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hg' : ∀ u v, h (g u) (g v) = h u v := hg
  have hint : ∀ x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L,
      h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x hx
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
    exact hx
  have hexp : ∀ v : V, v = ∑ i, h (e i) v • e i := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range e) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [he, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' Finset.univ j]
      simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul a x _ hx =>
      simp only [map_smul, smul_eq_mul, mul_smul]
      rw [← Finset.smul_sum, ← hx]
  apply le_antisymm
  · intro z hz
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hz
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hz
    have hall : ∀ v ∈ Submodule.span (𝓞 K) (Set.range e), g v ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hge j
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [Formalism.HermitianLatticesTheory.isomAct_smul]; exact Submodule.smul_mem _ a hx
    have h1 := hall _ hsx
    rw [Formalism.HermitianLatticesTheory.isomAct_smul, LinearEquiv.apply_symm_apply] at h1
    have h2 : z ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) p) (Formalism.HermitianLatticesTheory.loc (K := K) p L) :=
      Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s, hs, h1⟩
    unfold Formalism.HermitianLatticesTheory.loc at h2 ⊢
    rwa [Formalism.HermitianLatticesTheory.locBasic_locS_idem] at h2
  · intro m hm
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hexp (g.symm m)]
    refine Submodule.sum_mem _ fun i _ => ?_
    apply smul_mem_loc hp
    · have := hint m hm _ (hge i)
      rwa [← hg', LinearEquiv.apply_symm_apply]
    · exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.HermitianLattices.Ext.L3.WA
