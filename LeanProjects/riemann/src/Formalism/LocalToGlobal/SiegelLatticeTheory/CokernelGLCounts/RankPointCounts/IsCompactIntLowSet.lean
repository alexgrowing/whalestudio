import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CommonDenom

noncomputable section

open scoped Classical
open NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.ProdEP2Uni

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_of_norm {G : Type} [Group G] (A B' : Subgroup G) (s : G) (hAB' : A ≤ B') (hB : cj s B' = B')
    (hf : A.relIndex B' ≠ 0) : IdxRatio A (cj s A) = 1 := by
  have hA'le : cj s A ≤ B' := hB ▸ cj_le hAB'
  have hA'idx : (cj s A).relIndex B' = A.relIndex B' := by rw [← relIndex_cj s A B', hB]
  have e2 := idxCocycle G A (cj s A) B' hA'le (by rw [hA'idx]; exact hf)
  have e3 := idxCocycle G A A B' hAB' hf
  rw [idxRatio_self] at e3
  rw [e2, hA'idx, ← e3]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

section Mat

def dg (x : (D.s.atP p).Ep) : MP p := Matrix.diagonal fun i => x ^ (i : ℕ)

theorem dg_mul_dg (x y : (D.s.atP p).Ep) : (dg x : MP p) * dg y = dg (x * y) := by
  simp only [dg, Matrix.diagonal_mul_diagonal, mul_pow]

theorem dg_one : (dg 1 : MP p) = 1 := by
  simp [dg]

theorem dg_entry (x y : (D.s.atP p).Ep) (m : MP p) (i j : Fin (D.R.rS + 1)) :
    (dg x * m * dg y) i j = x ^ (i : ℕ) * m i j * y ^ (j : ℕ) := by
  simp only [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem pow_inv_pow {a : (D.s.atP p).Fp} (ha : a ≠ 0) (k : ℕ) :
    (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ k * (algebraMap _ (D.s.atP p).Ep a) ^ k = 1 := by
  rw [← mul_pow, ← map_mul, inv_mul_cancel₀ ha, map_one, one_pow]

theorem pow_scale {a : (D.s.atP p).Fp} (ha : a ≠ 0) {i j : ℕ} (hij : j ≤ i) :
    (algebraMap _ (D.s.atP p).Ep a) ^ i * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ j =
      (algebraMap _ (D.s.atP p).Ep a) ^ (i - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), mul_assoc,
    mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), pow_inv_pow ha, mul_one]

def tU (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GLp p :=
  ⟨dg (algebraMap _ _ a), dg (algebraMap _ _ a⁻¹),
    by rw [dg_mul_dg, ← map_mul, mul_inv_cancel₀ ha, map_one, dg_one],
    by rw [dg_mul_dg, ← map_mul, inv_mul_cancel₀ ha, map_one, dg_one]⟩

def tG (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GG p := (tU a ha, MulOpposite.op (tU a ha))

def KD (a : (D.s.atP p).Fp) (ha : a ≠ 0) : Subgroup (GG p) := cj (tG a ha) (KP M p)

theorem mem_KP {x : GG p} : x ∈ KP M p ↔
    TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧ TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p) := Iff.rfl

theorem mem_KD {a : (D.s.atP p).Fp} (ha : a ≠ 0) {x : GG p} : x ∈ KD M a ha ↔
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a)) := by
  rw [KD, mem_cj]
  show TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * (((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a))) ↔ _
  rw [← Matrix.mul_assoc]

end Mat

section Scale

variable {a : (D.s.atP p).Fp}

theorem intLow_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : TieN.IntLow (M p) l) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hl.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, hl.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (j : ℕ) i with h | h
    · rw [mul_right_comm, pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hl.2.2 i j)
    · rw [hl.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : TieN.IntUp (M p) ρ) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hρ.1 i, mul_one, pow_inv_pow ha]
  · rw [dg_entry, hρ.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (i : ℕ) j with h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hρ.2.2 i j)
    · rw [hρ.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : IsLoUni l)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * l i j ∈ (M p).R) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hl i i).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, (hl i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · rw [mul_right_comm, pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) - j = k + 1 := ⟨(i : ℕ) - j - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : j = i := Fin.ext h
      subst hij
      rw [(hl j j).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hl i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : IsUpUni ρ)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hρ i i).2 rfl, mul_one, pow_inv_pow ha]
  · rw [dg_entry, (hρ i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) - i = k + 1 := ⟨(j : ℕ) - i - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : i = j := Fin.ext h
      subst hij
      rw [(hρ i i).2 rfl, mul_one, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hρ i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_of_scaled (ha : a ≠ 0) {l : MP p}
    (h : TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹))) (hR : ∀ i j, l i j ∈ (M p).R) :
    TieN.IntLow (M p) l := by
  have hu : ∀ i j, l i j = (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) *
      (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc l i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * l i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem intUp_of_scaled (ha : a ≠ 0) {ρ : MP p}
    (h : TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a))) (hR : ∀ i j, ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) ρ := by
  have hu : ∀ i j, ρ i j = (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ) *
      (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc ρ i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * ρ i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem KP_le_KD (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) : KP M p ≤ KD M a ha := fun x hx =>
  (mem_KD M ha).2 ⟨intLow_scale M ha haO hx.1, intUp_scale M ha haO hx.2⟩

end Scale

section Top

theorem isClosed_imp {X : Type*} [TopologicalSpace X] (P : Prop) {s : Set X} (hs : IsClosed s) :
    IsClosed {x | P → x ∈ s} := by
  by_cases h : P
  · simpa [h] using hs
  · simp [h]

include M in
theorem isClosed_loUni (p : PlF D) : IsClosed {m : MP p | IsLoUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsLoUni m} = ⋂ i, ⋂ j, ({m : MP p | i < j → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsLoUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

include M in
theorem isClosed_upUni (p : PlF D) : IsClosed {m : MP p | IsUpUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsUpUni m} = ⋂ i, ⋂ j, ({m : MP p | j < i → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsUpUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

theorem isClosed_intLowSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntLow (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | i < j → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntLow, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isClosed_intUpSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntUp (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | j < i → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntUp, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isCompact_intLowSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intLowSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_intUpSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intUpSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_KP (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) : IsCompact (KP M p : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  let ι : GG p → (MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ) :=
    fun x => (Units.embedProduct _ x.1, Units.embedProduct _ x.2.unop)
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap
      (Units.isClosedEmbedding_embedProduct.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hIL := isCompact_intLowSet M hRc
  have hIU := isCompact_intUpSet M hRc
  let Kset : Set ((MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ)) :=
    ({l : MP p | TieN.IntLow (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntLow (M p) l})) ×ˢ
      ({l : MP p | TieN.IntUp (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntUp (M p) l}))
  have hK : IsCompact Kset :=
    (hIL.prod (hIL.image MulOpposite.continuous_op)).prod (hIU.prod (hIU.image MulOpposite.continuous_op))
  have hcl : IsClosed (KP M p : Set (GG p)) :=
    ((isClosed_intLowSet M hRc.isClosed).preimage (Units.continuous_val.comp continuous_fst)).inter
      ((isClosed_intUpSet M hRc.isClosed).preimage
        (Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)))
  have hsub : (KP M p : Set (GG p)) ⊆ ι ⁻¹' Kset := by
    intro x hx
    have hx1 := ((mem_KP M).1 hx).1
    have hx2 := ((mem_KP M).1 hx).2
    have hy := (mem_KP M).1 ((KP M p).inv_mem hx)
    exact ⟨⟨hx1, _, hy.1, rfl⟩, hx2, _, hy.2, rfl⟩
  exact (hι.isCompact_preimage hK).of_isClosed_subset hcl hsub

theorem isCompact_KD (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0) :
    IsCompact (KD M a ha : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  rw [KD, cj, Subgroup.coe_map]
  refine (isCompact_KP M hRc).image ?_
  have e : ((MulAut.conj (tG a ha)⁻¹).toMonoidHom : GG p → GG p) =
      fun x => (tG a ha)⁻¹ * x * (tG a ha)⁻¹⁻¹ := by
    funext x
    rfl
  rw [e]
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem relIndex_ne_zero (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0)
    (S' : Subgroup (GG p)) (hS : IsClosed (S' : Set (GG p))) :
    (KP M p ⊓ S').relIndex (KD M a ha ⊓ S') ≠ 0 := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have hBc : IsCompact ((KD M a ha ⊓ S' : Subgroup (GG p)) : Set (GG p)) := (isCompact_KD M hRc ha).inter_right hS
  haveI : CompactSpace (KD M a ha ⊓ S' : Subgroup (GG p)) := isCompact_iff_compactSpace.1 hBc
  have hR : IsOpen ((M p).R : Set (D.s.atP p).Ep) := PI.ProdFormulaE.ROpen.isOpen_R (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  let Eset : Set (GG p) := (⋂ i, ⋂ j, (fun x : GG p => ((x.1 : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)) ∩
    ⋂ i, ⋂ j, (fun x : GG p => ((x.2.unop : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)
  have hE : IsOpen Eset :=
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h1.matrix_elem i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h2.matrix_elem i j))
  have hopen : IsOpen (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) :
      Set (KD M a ha ⊓ S' : Subgroup (GG p))) := by
    have e : (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) : Set (KD M a ha ⊓ S' : Subgroup (GG p))) =
        Subtype.val ⁻¹' Eset := by
      ext y
      obtain ⟨hK, hS'⟩ := Subgroup.mem_inf.1 y.2
      rw [mem_KD] at hK
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Set.mem_preimage, Eset,
        Set.mem_inter_iff, Set.mem_iInter, mem_KP]
      constructor
      · rintro ⟨⟨hl, hu⟩, -⟩
        exact ⟨hl.2.2, hu.2.2⟩
      · rintro ⟨hl, hu⟩
        exact ⟨⟨intLow_of_scaled M ha hK.1 hl, intUp_of_scaled M ha hK.2 hu⟩, hS'⟩
    rw [e]
    exact hE.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  show ((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S')).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem idxRatio_norm (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) (S' : Subgroup (GG p))
    (hS : IsClosed (S' : Set (GG p))) (c : GG p) (hc1 : IsLoUni ((c.1 : GLp p) : MP p))
    (hc2 : IsUpUni ((c.2.unop : GLp p) : MP p)) (hcS : cj c S' = S') :
    IdxRatio (KP M p ⊓ S') (cj c (KP M p ⊓ S')) = 1 := by
  haveI := (D.s.atP p).lf
  obtain ⟨a, ha0, haR⟩ := common_denom (M p)
    (fun k : (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕ (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) =>
      Sum.elim (fun ij => ((c.1 : GLp p) : MP p) ij.1 ij.2) (fun ij => ((c.2.unop : GLp p) : MP p) ij.1 ij.2) k)
  have ha : (a : (D.s.atP p).Fp) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hcK : c ∈ KD M (a : (D.s.atP p).Fp) ha :=
    (mem_KD M ha).2 ⟨intLow_scale_of M ha a.2 hc1 fun i j => haR (Sum.inl (i, j)),
      intUp_scale_of M ha a.2 hc2 fun i j => haR (Sum.inr (i, j))⟩
  have hB : cj c (KD M (a : (D.s.atP p).Fp) ha ⊓ S') = KD M (a : (D.s.atP p).Fp) ha ⊓ S' := by
    ext g
    rw [mem_cj, Subgroup.mem_inf, Subgroup.mem_inf, ← mem_cj, ← mem_cj, cj_self hcK, hcS]
  exact unimod_of_norm _ _ c (inf_le_inf_right S' (KP_le_KD M ha a.2)) hB (relIndex_ne_zero M hRc ha S' hS)

theorem isClosed_StP (w : Point D.host.E (D.R.rS + 1)) :
    IsClosed ((StP M δ u u' w p : Subgroup (GG p)) : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  exact ((isClosed_loUni M p).preimage h1).inter (((isClosed_upUni M p).preimage h2).inter
    (isClosed_eq ((h1.mul continuous_const).mul h2) continuous_const))

theorem unimodAt_holds (w : Point D.host.E (D.R.rS + 1)) : UnimodAt M δ u u' (p := p) w := by
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).char0
  have hRc := R_compact (M p)
  intro s hs
  have hAg : Ag M δ u u' (p := p) w = KP M p ⊓ StP M δ u u' w p := by
    ext x
    rw [Ag, Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_KP M).2 hy, y.2⟩
    · rintro ⟨hK, hS⟩
      exact ⟨⟨x, hS⟩, hK, rfl⟩
  rw [hAg]
  exact idxRatio_norm M hRc _ (isClosed_StP M δ u u' w) s hs.1 hs.2.1 (cj_self hs)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem locIdxC_of_countAt (h : ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p))) :
    LocIdxC M δ u u' F0 what₂ :=
  locIdxC_of_count M δ u u' F0 what₂ fun γ w F' L U hE p => ⟨h γ w F' L U hE p, unimodAt_holds M δ u u' w⟩

end Top

end Formalism.L2.SG.Pf.ProdEP2Uni
