import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdNBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomWt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_KO_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (hJ : J ≤ KO k n) (ho : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
  haveI : Finite ((KO k n) ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem N_one_apply_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (a b : n) : u.val (Sum.inl a) (Sum.inl b) = (1 : Matrix n n k) a b := by
  have := GlobalTheory.RootEx.prodN_inN_of_mem hu (Sum.inl a) (Sum.inl b) le_rfl
  simpa [Matrix.one_apply] using this

theorem mul_embX_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (u * embX c g).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem embX_mul_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (embX c g * u).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem intM_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {g : GL n k} (h : IntM g.val) :
    IntM (embX c g : GL (n ⊕ Fin c) k).val := by
  rintro (a | a) (b | b)
  · simpa [embX] using h a b
  · simp [embX]
  · simp [embX]
  · by_cases e : a = b
    · subst e; simp [embX]
    · simp [embX, Matrix.one_apply, e]

theorem prX_Cgrp_KO_one (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) :
    prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  rw [mem_prX]
  constructor
  · rintro ⟨u, hu, hC⟩
    have hw : u * embX c g ∈ KO k (n ⊕ Fin c) := by simpa using (mem_Cgrp.1 hC).2
    obtain ⟨h1, h2⟩ := mem_KO.1 hw
    refine mem_KO.2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← mul_embX_inl hu g a b]; exact h1 _ _
    · have hu' : u⁻¹ ∈ N k n c 1 := inv_mem hu
      have e : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      rw [← embX_mul_inl hu' g⁻¹ a b, ← e]; exact h2 _ _
  · intro hg
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, mem_Cgrp]
    refine ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    obtain ⟨h1, h2⟩ := mem_KO.1 hg
    refine mem_KO.2 ⟨intM_embX h1, ?_⟩
    rw [← map_inv]; exact intM_embX h2

theorem reGL_symm_mem_KO_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twistChain_lev_zero {s : ℕ} {t κ : Type} [Fintype t] [DecidableEq t] [Fintype κ] [DecidableEq κ]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ := by
  ext x
  change (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J ↔ _
  rw [mem_parahoric]
  have e : (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    simp [LatFrame.conj, plainFrame]
    rfl
  rw [e, reGL_symm_mem_KO_iff]
  exact ⟨fun H => H.1, fun H => ⟨H, fun i _ => i.1.elim0⟩⟩

end GlobalTheory.BottomWt

namespace GlobalTheory.QTw
open GlobalTheory.BottomWt

theorem QExt.bottom_one : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  intro D c v B PP G χ E
  have hz : E.A 0 G.s (zero_add _) = {1} := E.reps.zero _ _
  have hrep : ∀ α, E.rep 0 G.s (zero_add _) α = 1 := fun α => by
    have := (E.rep_bij 0 G.s (zero_add _)).mapsTo (Set.mem_univ α)
    rw [hz] at this
    exact this
  have hJ0 : ∀ c h, ((G.T E.δ E.tame E.η).lev 0 c h).J = KO G.k _ := fun c h =>
    twistChain_lev_zero E.δ E.tame E.η c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_one_iff]
    have h1 : (1 : GL _ G.k) ∈ E.A 0 G.s (zero_add _) := by rw [hz]; rfl
    obtain ⟨x, -, -⟩ := (E.rep_bij 0 G.s (zero_add _)).surjOn h1
    exact ⟨x, fun y => (E.rep_bij 0 G.s (zero_add _)).injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hrep y).trans (hrep x).symm)⟩
  · intro α
    rw [E.wt_mid 0 G.s (zero_add _) α, hrep α, hJ0, prX_Cgrp_KO_one, (E.haar 0).2]
    simp
  · rw [E.idx_mid 0 (G.s + 1) (zero_add _), hJ0]
    exact Subgroup.relIndex_self _
  · intro j hj
    rcases Nat.lt_or_ge j (G.s + 2) with hl | hl
    · rw [E.idx_mid j (G.s + 1 - j) (by omega)]
      exact relIndex_KO_ne_zero (E.le _ _ _) (E.reg.2.2 _ _ _).1
    · obtain rfl : j = G.s + 1 + 1 := by omega
      rw [E.idx_top]
      exact relIndex_KO_ne_zero E.leT E.openT

end GlobalTheory.QTw
