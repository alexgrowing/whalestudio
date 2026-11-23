import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitAtUnitArch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtUnitArchOfMemIdelesAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler GlobalTheory.ConeSoB GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleRestr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem comp_of_mem_fin {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v)) :
    (∀ w, compInf F E w (l : AE F E) = 1) ∧ ∀ u, u ≠ v → compFin F E u (l : AE F E) = 1 := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hl
  exact ⟨fun w => by have := h1 w; rwa [map_sub, map_one, sub_eq_zero] at this,
    fun u hu => by have := h2 u hu; rwa [map_sub, map_one, sub_eq_zero] at this⟩

theorem comp_of_mem_inf {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evI F)) (u : Pl F) :
    compFin F E u (l : AE F E) = 1 := by
  have := at_evI_iff.1 hl u
  rwa [map_sub, map_one, sub_eq_zero] at this

example (x : (AE F E)ˣ) (v : Pl F) : (GlobalTheory.Doubling.unitFin F E v x : Fv F v ⊗[F] E) = compFin F E v x := rfl

end GlobalTheory.IdeleRestr

namespace GlobalTheory.IdeleRestr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_adele_comp (z : AE F E) (c : ∀ v : Pl F, Fv F v ⊗[F] E)
    (hc : ∀ᶠ v in cofinite, c v ∈ intLoc F E v) :
    ∃ y : AE F E, (∀ w, compInf F E w y = compInf F E w z) ∧ ∀ v, compFin F E v y = c v := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  have hr : ∀ j, ∀ᶠ v in cofinite, (Algebra.TensorProduct.basis (Fv F v) b).repr (c v) j ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) := fun j =>
    (hc.and (GlobalTheory.IdeleCyl.eventually_repr_mem_of_mem_intLoc F E j)).mono fun v h => h.2 _ h.1
  let r : Fin (Module.finrank F E) → Af F := fun j =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (c v) j, hr j⟩
  let q : Fin (Module.finrank F E) → AF F := fun j => ((0, r j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  refine ⟨eInf F • z + ∑ j, q j ⊗ₜ[F] b j, fun w => ?_, fun v => ?_⟩
  · rw [map_add, compInf_smul, GlobalTheory.IdeleCyl.evInf_eInf, one_smul, map_sum]
    refine (add_eq_left).2 (Finset.sum_eq_zero fun j _ => ?_)
    change evInf F w (q j) ⊗ₜ[F] b j = 0
    rw [show evInf F w (q j) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul]
  · rw [map_add, compFin_smul, show evFin F v (eInf F) = 0 from map_zero (evalV F v), zero_smul, zero_add, map_sum]
    conv_rhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (c v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    change evFin F v (q j) ⊗ₜ[F] b j = _
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

end GlobalTheory.IdeleRestr

namespace GlobalTheory.IdeleRestr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idele_comp (a : (AE F E)ˣ) (c : ∀ v : Pl F, (Fv F v ⊗[F] E)ˣ)
    (hc : ∀ᶠ v in cofinite, ((c v : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ (((c v)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v)) :
    ∃ x : (AE F E)ˣ, (∀ w, GlobalTheory.Doubling.unitInf F E w x = GlobalTheory.Doubling.unitInf F E w a) ∧
      ∀ v, GlobalTheory.Doubling.unitFin F E v x = c v := by
  obtain ⟨y, hy1, hy2⟩ := exists_adele_comp (a : AE F E) (fun v => (c v : Fv F v ⊗[F] E)) (hc.mono fun _ h => h.1)
  obtain ⟨y', hy1', hy2'⟩ := exists_adele_comp ((a⁻¹ : (AE F E)ˣ) : AE F E)
    (fun v => (((c v)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) (hc.mono fun _ h => h.2)
  have h : y * y' = 1 := GlobalTheory.Doubling.adele_ext (fun w => by
      rw [map_mul, hy1 w, hy1' w, ← map_mul, Units.mul_inv, map_one])
    (fun v => by rw [map_mul, hy2 v, hy2' v, Units.mul_inv, map_one])
  refine ⟨⟨y, y', h, by rw [mul_comm]; exact h⟩, fun w => Units.ext (hy1 w), fun v => Units.ext (hy2 v)⟩

end GlobalTheory.IdeleRestr

open GlobalTheory.IdeleRestr in

theorem GlobalTheory.IdeleRestr.isRestrGroup_ideles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    GlobalTheory.RestrMeas.IsRestrGroup (X := (AE F E)ˣ) (W := Unit) (V := Pl F)
      (fun _ => (unitArch F E).codRestrict (idelesAt E (evI F)) unitArch_mem)
      (fun v => (unitAt E v).codRestrict (idelesAt E (evFin F v)) (unitAt_mem v))
      (fun v => (unitsAt E v).subgroupOf (idelesAt E (evFin F v))) := by
  intro F E _ _ _ _ _
  obtain ⟨hcf, hca⟩ := continuous_unitAt_unitArch F E
  refine ⟨fun _ => hca.subtype_mk _, fun v => (hcf v).subtype_mk _, fun v => (isCompact_isOpen_unitsAt v).2,
    fun v => (isCompact_isOpen_unitsAt v).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y ha hf
    have hA : unitArch F E x = unitArch F E y := congrArg Subtype.val (ha ())
    have hF : ∀ v, unitAt E v x = unitAt E v y := fun v => congrArg Subtype.val (hf v)
    refine GlobalTheory.Doubling.idele_ext (fun w => Units.ext ?_) fun v => Units.ext ?_
    · exact (GlobalTheory.IdeleCyl.compInf_unitArch w x).symm.trans
        ((congrArg (fun l : (AE F E)ˣ => compInf F E w (l : AE F E)) hA).trans (GlobalTheory.IdeleCyl.compInf_unitArch w y))
    · exact (GlobalTheory.IdeleCyl.compFin_unitAt v x).symm.trans
        ((congrArg (fun l : (AE F E)ˣ => compFin F E v (l : AE F E)) (hF v)).trans (GlobalTheory.IdeleCyl.compFin_unitAt v y))
  · intro x
    exact (eventually_unitAt_mem_unitsAt F E x).mono fun v h => Subgroup.mem_subgroupOf.2 h
  · intro a y hy
    have hy' : ∀ᶠ v in cofinite, ((GlobalTheory.Doubling.unitFin F E v (y v).1 : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
        (((GlobalTheory.Doubling.unitFin F E v (y v).1)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v) :=
      hy.mono fun v h => by
        have h' := mem_unitsAt.1 (Subgroup.mem_subgroupOf.1 h)
        exact ⟨h'.2.1, by rw [← map_inv]; exact h'.2.2⟩
    obtain ⟨x, hx1, hx2⟩ := exists_idele_comp (a ()).1 (fun v => GlobalTheory.Doubling.unitFin F E v (y v).1) hy'
    refine ⟨x, fun _ => Subtype.ext ?_, fun v => Subtype.ext ?_⟩
    · show unitArch F E x = (a ()).1
      refine GlobalTheory.Doubling.idele_ext (fun w => Units.ext ?_) fun v => Units.ext ?_
      · change compInf F E w (unitArch F E x : AE F E) = compInf F E w ((a ()).1 : AE F E)
        rw [GlobalTheory.IdeleCyl.compInf_unitArch]
        exact congrArg Units.val (hx1 w)
      · change compFin F E v (unitArch F E x : AE F E) = compFin F E v ((a ()).1 : AE F E)
        rw [comp_of_mem_inf (unitArch_mem x), comp_of_mem_inf (a ()).2]
    · show unitAt E v x = (y v).1
      refine GlobalTheory.Doubling.idele_ext (fun w => Units.ext ?_) fun u => Units.ext ?_
      · change compInf F E w (unitAt E v x : AE F E) = compInf F E w ((y v).1 : AE F E)
        rw [(comp_of_mem_fin (unitAt_mem v x)).1, (comp_of_mem_fin (y v).2).1]
      · change compFin F E u (unitAt E v x : AE F E) = compFin F E u ((y v).1 : AE F E)
        by_cases hu : u = v
        · subst hu
          rw [GlobalTheory.IdeleCyl.compFin_unitAt]
          exact congrArg Units.val (hx2 u)
        · rw [(comp_of_mem_fin (unitAt_mem v x)).2 u hu, (comp_of_mem_fin (y v).2).2 u hu]
  · exact isOpen_setOf_forall_unitAt_mem_unitsAt F E
  · intro C hC
    have h := GlobalTheory.IdeleCyl.isCompact_cyl F E ∅ (Subtype.val '' C ()) (fun _ => ∅)
      ((hC ()).image continuous_subtype_val) (fun v hv => absurd hv (Finset.notMem_empty v))
    convert h using 1
    ext l
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1 (), rfl⟩, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => Subgroup.mem_subgroupOf.1 (h2 v)⟩
    · rintro ⟨⟨m, hm, hml⟩, -, h3⟩
      refine ⟨fun u => ?_, fun v => Subgroup.mem_subgroupOf.2 (h3 v (Finset.notMem_empty v))⟩
      cases u
      convert hm
      exact Subtype.ext hml.symm
