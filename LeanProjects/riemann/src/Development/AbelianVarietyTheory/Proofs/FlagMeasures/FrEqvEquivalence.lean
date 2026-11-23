import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometryStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameEqv
open AdaptInv
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem map_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) {x : V} (hx : x ∈ G.Xa k) : n x ∈ G'.Xa k := by
  have key : G.Xa k ≤ (G'.Xa k).comap (n : V →ₗ[K] V) := by
    show Submodule.span K _ ≤ _
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.val < k := hb
    have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
    have h2 : n (G.e b.castSucc) =
        (n (G.e b.castSucc) - G'.e b.castSucc) + G'.e b.castSucc := by abel
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [h2]
    exact (G'.Xa k).add_mem (xa_mono G' hb'.le h1) (e_mem_xa G' b hb')
  exact key hx

theorem symm_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) : ∀ x ∈ G'.Xa k, n.symm x ∈ G.Xa k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    have key : G'.Xa k ≤ (G.Xa k).comap (n.symm : V →ₗ[K] V) := by
      show Submodule.span K _ ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < k := hb
      have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
      have h2 := ih b.val hb' _ h1
      have e1 : n.symm (G'.e b.castSucc) =
          G.e b.castSucc - n.symm (n (G.e b.castSucc) - G'.e b.castSucc) := by
        rw [map_sub, LinearEquiv.symm_apply_apply, sub_sub_cancel]
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [e1]
      exact (G.Xa k).sub_mem (e_mem_xa G b hb') (xa_mono G hb'.le h2)
    exact key hx

theorem symm_gr {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (a : Fin (r + 1)) : n.symm (G'.e a) - G.e a ∈ G.Xa a.val := by
  have h1 := symm_xa h a.val _ (h a)
  have e1 : n.symm (G'.e a) - G.e a = -(n.symm (n (G.e a) - G'.e a)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
  rw [e1]
  exact (G.Xa a.val).neg_mem h1

theorem inN_gr {F : FlagD H r} {n : V ≃ₗ[K] V} (h : F.InN (n : V →ₗ[K] V)) (a : Fin (r + 1)) :
    n (F.e a) - F.e a ∈ F.Xa a.val := by
  induction a using Fin.lastCases with
  | last =>
    rw [Fin.val_last]
    exact h.2.2.2 _ F.zperp
  | cast b =>
    rw [Fin.coe_castSucc]
    exact h.2.2.1 b

theorem gr_comp {G G' M : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (hM : SameGr G M) (a : Fin (r + 1)) : n (M.e a) - G'.e a ∈ G'.Xa a.val := by
  have e1 : n (M.e a) - G'.e a = n (M.e a - G.e a) + (n (G.e a) - G'.e a) := by
    rw [map_sub]; abel
  rw [e1]
  exact (G'.Xa a.val).add_mem (map_xa h a.val (hM a)) (h a)
end

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem frEqv_equivalence (F : FlagD H r) (Λ : Submodule (𝓞 K) V) : Equivalence (FrEqv F Λ) := by
  refine ⟨fun G => ⟨1, GlobalTheory.UnipStab.inN_one, one_smul _ _, fun a => by simp⟩, ?_, ?_⟩
  · rintro G G' ⟨n, hn, hΛ, hG⟩
    refine ⟨n⁻¹, GlobalTheory.UnipStab.inN_inv hn, ?_, fun a => symm_gr hG a⟩
    conv_lhs => rw [← hΛ]
    exact inv_smul_smul n Λ
  · rintro G G' G'' ⟨n, hn, hΛ, hG⟩ ⟨m, hm, hΛ', hG'⟩
    refine ⟨m * n, GlobalTheory.UnipStab.inN_mul hm hn, by rw [mul_smul, hΛ, hΛ'], fun a => ?_⟩
    have e1 : (m * n) (G.e a) - G''.e a = m (n (G.e a) - G'.e a) + (m (G'.e a) - G''.e a) := by
      rw [LinearEquiv.mul_apply, map_sub]; abel
    rw [e1]
    exact (G''.Xa a.val).add_mem (map_xa hG' a.val (hG a)) (hG' a)

theorem move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G G' : FlagD H r} {𝔡 : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (h : FrEqv F Λ G G') (N : NF H r) (hN : Adapt F G 𝔡 N) :
    ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧
      ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  obtain ⟨n, hn, hΛ, hG⟩ := h
  have hiso : n ∈ isomGrp H := (mem_isomGrp H n).2 fun x y => hn.1 x y
  obtain ⟨N', he, -, -, -, hd, -, hrest⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N n hiso
  refine ⟨N', ⟨hd.trans hN.1, fun a => ?_, fun a => ?_⟩, ?_, fun g => ?_⟩
  · rw [(he a).1]
    have e1 : n (N.F.e a) - F.e a = n (N.F.e a - F.e a) + (n (F.e a) - F.e a) := by
      rw [map_sub]; abel
    rw [e1]
    exact (F.Xa a.val).add_mem (GlobalTheory.UnipStab.map_Xa hn a.val (hN.2.1 a)) (inN_gr hn a)
  · rw [(he a).2]
    exact gr_comp hG hN.2.2 a
  · have h1 := (hrest 0 Λ).1
    rwa [hΛ] at h1
  · have h1 := hrest g Λ
    rw [hΛ] at h1
    exact ⟨h1.2.1, h1.2.2⟩

end GlobalTheory.DegAsm.FrameEqv

namespace GlobalTheory.DegAsm
open FrameEqv

theorem frEqv_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), Equivalence (FrEqv F Λ) ∧ ∀ G G' : FlagD H r, FrEqv F Λ G G' → omI F G 𝔡 Λ = omI F G' 𝔡 Λ ∧ ∀ N : NF H r, Adapt F G 𝔡 N → ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧ ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r F 𝔡 Λ
  refine ⟨frEqv_equivalence F Λ, fun G G' h => ⟨?_, fun N hN => move hK h N hN⟩⟩
  have sub : ∀ {G G' : FlagD H r}, FrEqv F Λ G G' →
      (fun N : NF H r => N.om Λ) '' {N | Adapt F G 𝔡 N} ⊆
        (fun N : NF H r => N.om Λ) '' {N | Adapt F G' 𝔡 N} := by
    intro G G' h x hx
    obtain ⟨N, hN, rfl⟩ := hx
    obtain ⟨N', hN', hom, -⟩ := move hK h N hN
    exact ⟨N', hN', hom⟩
  unfold omI
  rw [Set.Subset.antisymm (sub h) (sub ((frEqv_equivalence F Λ).symm h))]

end GlobalTheory.DegAsm
