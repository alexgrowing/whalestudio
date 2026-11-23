import Formalism.LocalRingCardinality.SpanPowerMembership.NZColE

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

variable {D : D7} (c : LatCmp D) {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts)

def TAbs (D : D7) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

theorem cand_of_VV {p : ℕ} (h : VV X K (aL L) (bL L) p ≠ ∅) : Cand D L K p := by
  unfold VV at h
  by_contra hc
  rw [if_neg fun h' => hc h'.1] at h
  exact h rfl

theorem VV_fin : {p | VV X K (aL L) (bL L) p ≠ ∅}.Finite := by
  refine (Set.finite_lt_nat ⌈L.sc.X'⌉₊).subset fun p hp => ?_
  have h1 := (cand_of_VV X K hp).2.1
  exact Nat.lt_ceil.mpr h1

theorem cmpN_mem_M (u w hg) (y : (D.div.Nu u).V) (hy : y ∈ DV.MramL D u) : c.cmpN u w hg y ∈ (D.gat u w hg).M := by
  rw [← c.cmp_M u w hg]
  exact Submodule.subset_span ⟨D.nuIn u y, hy, rfl⟩

theorem cmpN_mem_Vram (hv : c.VramDef Y) (u w hg) (y : (D.div.Nu u).V) : c.cmpN u w hg y ∈ Y.Vram u w hg := by
  have h1 : D.nuIn u y ∈ (D.fm u).ramSub := by rw [← D.nuIn_range u]; exact ⟨y, rfl⟩
  have h2 : c.cmpN u w hg y ∈ (Y.Vram u w hg : Set (D.gat u w hg).Fn) := by
    rw [hv u w hg]
    exact Submodule.subset_span ⟨D.nuIn u y, h1, rfl⟩
  exact h2

theorem NP_le (u w hg) : NP X Y K u w hg ≤ (D.gat u w hg).M ⊓ Y.Vram u w hg := by
  intro F hF
  unfold NP at hF
  obtain ⟨⟨-, h2⟩, h3⟩ := hF
  refine ⟨?_, h3⟩
  obtain ⟨F0, hF0, rfl⟩ := h2
  exact Submodule.smul_mem _ _ hF0

theorem exists_residueChar_pow_smul_mem (hv : c.VramDef Y) (u w hg) : ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NP X Y K u w hg := by
  refine ⟨⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat +
    ∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
      ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat, fun y hy => ?_⟩
  have hM := cmpN_mem_M c u w hg y hy
  have hV := cmpN_mem_Vram c Y hv u w hg y
  rw [pow_add, mul_smul]
  unfold NP
  refine ⟨⟨Submodule.smul_mem _ _ (Submodule.subset_span ⟨∅, Finset.empty_subset _, _, hM, ?_⟩), ?_⟩,
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hV)⟩
  · simp [yProd]
  · exact ⟨_, Submodule.smul_mem _ _ hM, rfl⟩

def nuDataOf (hv : c.VramDef Y) (hT : TAbs D) : NuData c where
  S p := VV X K (aL L) (bL L) p ≠ ∅
  S_fin := VV_fin X K
  NPf := NP X Y K
  exists_residueChar_pow_smul_mem := exists_residueChar_pow_smul_mem c X Y K hv
  T_abs := hT

def lenOf (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℚ :=
  ((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ)

variable (hv : c.VramDef Y) (hT : TAbs D)

end Formalism.BasicNotions.Examples₂.NZ
