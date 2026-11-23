import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem indexTwo_unitary (y : L) (hy : σ y + y = 0) :
    cT σ !![1, y; 0, 1] * antiJ L 2 * !![1, y; 0, 1] = antiJ L 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [add_comm]; exact hy

theorem indexTwo_exists_hom (σ : L →+* L) (T : AddSubgroup L) (hT : ∀ y, y ∈ T ↔ σ y + y = 0) :
    ∃ ψ : Multiplicative T →* GU σ 2,
      ∀ y, mat (ψ y) = !![1, (y.toAdd : L); 0, 1] := by
  have h : ∀ y : Multiplicative T,
      ∃ g : GU σ 2, mat g = !![1, (y.toAdd : L); 0, 1] := fun y =>
    exists_mat _ (indexTwo_unitary _ ((hT _).1 y.toAdd.2))
  choose f hf using h
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, hf⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, AddSubgroup.coe_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem indexTwo_mem_root (g : GU σ 2) :
    g ∈ rootU σ ![0, 0] ↔ mat g = !![1, mat g 0 1; 0, 1] := by
  constructor
  · intro h
    have h1 : ∀ i j : Fin 2, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 2) (Fin 2) L) i j := h.1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1 0 0 (by simp)
    · simp
    · simpa using h1 1 0 (by simp)
    · simpa using h1 1 1 (by simp)
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [h]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp at hij

theorem indexTwo_trace (g : GU σ 2) (y : L) (h : mat g = !![1, y; 0, 1]) : σ y + y = 0 := by
  have h1 : cT σ (mat g) * antiJ L 2 * mat g = antiJ L 2 := g.2
  rw [h] at h1
  have := congrFun (congrFun h1 1) 1
  simpa [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using this

theorem indexTwo_conj {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by
  have e : mat s * mat g = !![1, ϖ * (ϖ * y); 0, 1] * mat s := by
    rw [hs, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [mat_mul, mat_mul, e, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

end

theorem indexTwo_of_traceZeroIndex (H : TraceZeroIndex) : IndexTwo := by
  intro L _ _ ϖ σ q hU s hs
  have hq := H L ϖ σ q hU
  have h0 : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  have memT : ∀ y, y ∈ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔ σ y + y = 0 := fun y => Iff.rfl
  generalize (σ.toAddMonoidHom + AddMonoidHom.id L).ker = T at hq memT
  obtain ⟨ψ, hψ⟩ := indexTwo_exists_hom σ T memT
  set U := (intL L).toAddSubgroup ⊓ T with hUdef
  set m : L →+ L := AddMonoidHom.mulLeft ϖ with hm
  have hmT : ∀ y, y ∈ T → ϖ * y ∈ T := fun y hy => by
    rw [memT] at hy ⊢
    rw [map_mul, hU.2.2.1, ← mul_add, hy, mul_zero]
  have hminj : Function.Injective m := mul_right_injective₀ h0
  have hle : U.map m ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(intL L).mul_mem hϖ hy.1, hmT y hy.2⟩
  have h2 : ((U.map m).map m).relIndex U = q ^ 2 := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ (U.map m) _ (AddSubgroup.map_mono hle) hle,
      AddSubgroup.relIndex_map_map_of_injective _ _ hminj, hq, sq]
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := congrFun (congrFun ((hψ a).symm.trans ((congrArg mat hab).trans (hψ b))) 0) 1
    exact Multiplicative.toAdd.injective (Subtype.ext (by simpa using this))
  have e1 : KU σ 2 ⊓ rootU σ ![0, 0] = (AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨hK, hr⟩
      have hr' := (indexTwo_mem_root g).1 hr
      have ht := (memT _).2 (indexTwo_trace g _ hr')
      refine ⟨Multiplicative.ofAdd ⟨mat g 0 1, ht⟩, ⟨(mem_KU_iff hU.2.1 g).1 hK 0 1, ht⟩, mat_injective ?_⟩
      rw [hψ]; exact hr'.symm
    · rintro ⟨y, hy, rfl⟩
      have hy1 : (y.toAdd : L) ∈ intL L := hy.1
      refine ⟨(mem_KU_iff hU.2.1 _).2 fun i j => ?_, (indexTwo_mem_root _).2 ?_⟩
      · rw [hψ]
        fin_cases i <;> fin_cases j
        · exact one_mem _
        · exact hy1
        · exact zero_mem _
        · exact one_mem _
      · rw [hψ]; rfl
  have e2 : ((AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ).map (MulAut.conj s).toMonoidHom =
      (AddSubgroup.toSubgroup (((U.map m).map m).addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨ϖ * (ϖ * (y.toAdd : L)), hmT _ (hmT _ y.toAdd.2)⟩,
        ⟨_, ⟨_, hy, rfl⟩, rfl⟩, mat_injective ?_⟩
      rw [hψ]
      exact (indexTwo_conj h0 s _ hs _ (hψ y)).symm
    · rintro ⟨z, ⟨_, ⟨y, hy, rfl⟩, hz⟩, rfl⟩
      refine ⟨ψ (Multiplicative.ofAdd ⟨y, hy.2⟩), ⟨Multiplicative.ofAdd ⟨y, hy.2⟩, hy, rfl⟩, mat_injective ?_⟩
      refine (indexTwo_conj h0 s _ hs _ (hψ _)).trans ?_
      rw [hψ]
      exact congrArg (fun w => !![1, w; 0, 1]) hz
  rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup,
    AddSubgroup.relIndex_addSubgroupOf inf_le_right, h2]

end GlobalTheory.SatakeWeyl
