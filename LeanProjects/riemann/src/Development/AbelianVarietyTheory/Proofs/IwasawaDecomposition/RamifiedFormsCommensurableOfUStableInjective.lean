import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelCommensurable

theorem exists_nsmul_map_mem {K V W : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (A : Submodule (𝓞 K) W) (hA : A.FG) (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤)
    (f : W →ₗ[K] V) : ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, n • f x ∈ L := by
  classical
  obtain ⟨s, rfl⟩ := hA
  have h : ∀ x : W, ∃ n : ℕ, n ≠ 0 ∧ n • f x ∈ L := fun x =>
    GlobalTheory.Mem.Full.exists_nsmul_mem_of_span L (f x) (by rw [hL]; trivial)
  choose c hc0 hc using h
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_coe.1 hy)
    rw [hk, mul_comm, mul_smul]
    exact L.toAddSubmonoid.nsmul_mem (hc y) k
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact L.add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul K r y, map_smul, smul_comm, algebraMap_smul]
    exact L.smul_mem r hy

open GlobalTheory.LevelIndexCompare GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks in

theorem commensurable : ∀ (D : D7) (u : D.what₂.Word), (∀ v, ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)) → (∀ v, ∀ φ ∈ (D.mem u).A.Mram, LT.Uop D u 0 v φ = 0 → φ = 0) → ∀ w : D.what₂.places.Pl, ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧ ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x) := by
  classical
  intro D u hst hinj w
  have hex : ∀ v, ∃ g, IsScaledU D u w v g := fun v => (exists_isScaledU_iff D u w v).2 (hst v)
  choose g hg using hex
  haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  have hgi : ∀ v, IsUnit (g v) := by
    intro v
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hg v x
    rw [hx, Submodule.coe_zero, map_zero] at h1
    have h2 := (smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ (T_ne_zero D u))
    have h3 := hinj v _ x.2 h2
    exact Subtype.ext ((D.fm u).emb_inj 0 (h3.trans (map_zero _).symm))
  set G : Module.End D.what₂.LL (D.fm u).ramSub := ((LT.VVT D u w).toList.map g).prod ^ D.R.m with hG
  have hGu : IsUnit G := by
    refine IsUnit.pow _ (List.prod_isUnit fun a ha => ?_)
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact hgi v
  obtain ⟨H, hH⟩ := hGu.exists_right_inv
  have hmem : ∀ x, D.nuIn u x ∈ (D.fm u).ramSub := fun x => D.nuIn_range u ▸ ⟨x, rfl⟩
  let e : (D.div.Nu u).V →ₗ[D.what₂.LL] (D.fm u).ramSub := LinearMap.codRestrict _ (D.nuIn u) hmem
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ H ∘ₗ e)
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nsmul_map_mem (DV.MramL D u) (D.MramL_fg u) ((D.fm u).lat 0).L
    ((D.fm u).lat_good 0).2.2 ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e)
  refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)]
    have hL : (((n₁ * n₂) • H (e x) : (D.fm u).ramSub) : LT.Vl D u 0) ∈ ((D.fm u).lat 0).L := by
      rw [mul_comm, mul_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]
      exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem (h₁ x hx) n₂
    refine ⟨⟨_, ⟨Submodule.subset_span hL, ((n₁ * n₂) • H (e x)).2⟩⟩, ?_⟩
    show _ = ((G ((n₁ * n₂) • H (e x)) : (D.fm u).ramSub) : LT.Vl D u 0)
    rw [map_nsmul G, ← Module.End.mul_apply, hH, map_nsmul]
    rfl
  · rw [mem_Nlam_iff D u w g (fun v _ => hg v)] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨s, hs, hsy⟩ := D.inLoc_of_mem_locW w _ _ y.2.1
    obtain ⟨z, hz⟩ : (y : LT.Vl D u 0) ∈ LinearMap.range (D.nuIn u) := by
      rw [D.nuIn_range u]; exact y.2.2
    have hsm : ∀ t, D.nuIn u (s • t) = s • D.nuIn u t := fun t =>
      map_smul ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) s t
    have hzM : s • z ∈ DV.MramL D u := by
      show D.nuIn u (s • z) ∈ ((D.fm u).lat 0).L
      rw [hsm, hz]; exact hsy
    have h3 := h₂ _ hzM
    have hez : e z = incl D u w y := Subtype.ext hz
    have h4 : ((D.fm u).ramSub.subtype ∘ₗ G ∘ₗ e) (s • z) = s • D.nuIn u x := by
      rw [← algebraMap_smul D.what₂.LL s z, map_smul, algebraMap_smul, hy]
      show s • ((G (e z) : (D.fm u).ramSub) : LT.Vl D u 0) = _
      rw [hez]
    rw [h4] at h3
    refine ⟨s, hs, ?_⟩
    show D.nuIn u (s • (n₁ * n₂) • x) ∈ ((D.fm u).lat 0).L
    rw [hsm, map_nsmul, smul_comm, mul_smul]
    exact ((D.fm u).lat 0).L.toAddSubmonoid.nsmul_mem h3 n₁

end GlobalTheory.LevelCommensurable
