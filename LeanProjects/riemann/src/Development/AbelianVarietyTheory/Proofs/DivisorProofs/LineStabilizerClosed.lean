import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LineStabClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_line_iff {n : ℕ} (x : Fin n → E) {i : Fin n} (hi : x i ≠ 0) (v : Fin n → AE F E) :
    (∃ a : AE F E, v = a • incV F x) ↔ ∀ r, v r * incV F x i = v i * incV F x r := by
  have hu : IsUnit (incV F x i) := (Ne.isUnit hi).map (inclR (F := F) (AF F))
  constructor
  · rintro ⟨a, rfl⟩ r
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro h
    obtain ⟨c, hc⟩ := hu
    refine ⟨v i * (c⁻¹ : (AE F E)ˣ), funext fun r => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have := h r
    rw [← hc] at this
    calc v r = v r * c * (c⁻¹ : (AE F E)ˣ) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [this]; ring

theorem isClosed_line [TopologicalSpace (AE F E)] [ContinuousMul (AE F E)] [T2Space (AE F E)] {n : ℕ} (x : Fin n → E) {i : Fin n} (hi : x i ≠ 0) :
    IsClosed {v : Fin n → AE F E | ∃ a : AE F E, v = a • incV F x} := by
  have : {v : Fin n → AE F E | ∃ a : AE F E, v = a • incV F x} = ⋂ r, {v | v r * incV F x i = v i * incV F x r} := by
    ext v; simp only [Set.mem_setOf_eq, Set.mem_iInter]; exact mem_line_iff x hi v
  rw [this]
  exact isClosed_iInter fun r => isClosed_eq ((continuous_apply r).mul continuous_const) ((continuous_apply i).mul continuous_const)

variable (F E) in
theorem isClosed_lineStab_unip (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (hx : x ≠ 0) :
    IsClosed (GlobalTheory.IwLine.lineStab σ J x : Set (UA σ J)) ∧
    IsClosed {u : UA σ J | mat u *ᵥ incV F x = incV F x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x} := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  obtain ⟨i, hi'⟩ := Function.ne_iff.1 hx
  have hi : x i ≠ 0 := hi'
  have hL := isClosed_line (F := F) x hi
  have hm : Continuous fun g : UA σ J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ J => mat g⁻¹ := hm.comp continuous_inv
  have hu : IsUnit (incV F x i) := (Ne.isUnit hi).map (inclR (F := F) (AF F))
  constructor
  · have e : (GlobalTheory.IwLine.lineStab σ J x : Set (UA σ J)) =
        (fun g : UA σ J => mat g *ᵥ incV F x) ⁻¹' {v | ∃ a : AE F E, v = a • incV F x} ∩
        (fun g : UA σ J => mat g⁻¹ *ᵥ incV F x) ⁻¹' {v | ∃ a : AE F E, v = a • incV F x} := by
      ext g
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hg
        obtain ⟨a, ha⟩ := (GlobalTheory.IwLine.mem_lineStab σ J).1 hg
        obtain ⟨b, hb⟩ := (GlobalTheory.IwLine.mem_lineStab σ J).1 ((GlobalTheory.IwLine.lineStab σ J x).inv_mem hg)
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        have e1 : incV F x = (b * a) • incV F x := by
          calc incV F x = mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) := by
                rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
            _ = _ := by rw [ha, Matrix.mulVec_smul, hb, smul_smul, mul_comm]
        have e2 : incV F x i * 1 = incV F x i * (b * a) := by
          have := congrFun e1 i
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [mul_one, mul_comm]; exact this
        have hba : b * a = 1 := (hu.mul_left_cancel e2).symm
        exact (GlobalTheory.IwLine.mem_lineStab σ J).2 ⟨⟨a, b, by rw [mul_comm]; exact hba, hba⟩, ha⟩
    rw [e]
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  · have e : {u : UA σ J | mat u *ᵥ incV F x = incV F x ∧
        ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x} =
        {u : UA σ J | mat u *ᵥ incV F x = incV F x} ∩ ⋂ z, (fun u : UA σ J => mat u *ᵥ (incM F ι *ᵥ z) - incM F ι *ᵥ z) ⁻¹'
          {v | ∃ a : AE F E, v = a • incV F x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      refine and_congr Iff.rfl (forall_congr' fun z => exists_congr fun a => ?_)
      rw [sub_eq_iff_eq_add']
    rw [e]
    exact (isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_iInter fun z => hL.preimage ((hm.matrix_mulVec continuous_const).sub continuous_const))

end GlobalTheory.LineStabClosed
