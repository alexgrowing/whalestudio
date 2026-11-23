import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.IntermediateField
import GroundTheory.LocalFields.UnramifiedDefs
import GroundTheory.LocalFields.UnitsPowers

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance henselianLocalRing_integer : HenselianLocalRing 𝒪[K] where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    have := isAdicComplete_integer K
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

end Base

section Residue

variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]

theorem residue_aeval [Algebra 𝓀[K] 𝓀[M]]
    (h : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[M] (residue 𝒪[K] x) =
      residue 𝒪[M] (algebraMap 𝒪[K] 𝒪[M] x))
    (P : 𝒪[K][X]) (x : 𝒪[M]) :
    residue 𝒪[M] (aeval x P) = aeval (residue 𝒪[M] x) (P.map (residue 𝒪[K])) := by
  have hc : (algebraMap 𝓀[K] 𝓀[M]).comp (residue 𝒪[K]) =
      (residue 𝒪[M]).comp (algebraMap 𝒪[K] 𝒪[M]) := RingHom.ext h
  rw [aeval_def, aeval_def, eval₂_map, hc, hom_eval₂]

end Residue

theorem isScalarTower_residueField (K E L : Type*) [Field K] [ValuativeRel K] [Field E]
    [ValuativeRel E] [Field L] [ValuativeRel L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [ValuativeExtension K E] [ValuativeExtension E L]
    [ValuativeExtension K L] [Algebra 𝓀[K] 𝓀[E]] [Algebra 𝓀[E] 𝓀[L]] [Algebra 𝓀[K] 𝓀[L]]
    (h₁ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[E] (residue 𝒪[K] x) =
      residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] x))
    (h₂ : ∀ x : 𝒪[E], algebraMap 𝓀[E] 𝓀[L] (residue 𝒪[E] x) =
      residue 𝒪[L] (algebraMap 𝒪[E] 𝒪[L] x))
    (h₃ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] x) =
      residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)) :
    IsScalarTower 𝓀[K] 𝓀[E] 𝓀[L] := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [h₁, h₂, h₃, IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] 𝒪[L]]

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_lift_primitive :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧
      P.natDegree = residueDegree K L ∧ (P.map (residue 𝒪[K])).Separable ∧
      IntermediateField.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element 𝓀[K] 𝓀[L]
  have hbi : IsIntegral 𝓀[K] b := .of_finite _ _
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    (f := residue 𝒪[K]) (p := minpoly 𝓀[K] b)
    ((lifts_iff_coeff_lifts _).2 fun n ↦ residue_surjective _) (minpoly.monic hbi)
  have hsep : (minpoly 𝓀[K] b).Separable := Algebra.IsSeparable.isSeparable 𝓀[K] b
  obtain ⟨b0, rfl⟩ := residue_surjective (R := 𝒪[L]) b
  let Q := P.map (algebraMap 𝒪[K] 𝒪[L])
  have hQ : Q.Monic := hPmon.map _
  have h1 : Q.eval b0 ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl), hPmap, minpoly.aeval]
  have h2 : IsUnit (Q.derivative.eval b0) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl),
      ← derivative_map, hPmap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβ, hβb⟩ := HenselianLocalRing.is_henselian Q hQ b0 h1 h2
  have hres : residue 𝒪[L] β = residue 𝒪[L] b0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hβb
  refine ⟨β, P, hPmon, ?_, ?_, ?_, ?_⟩
  · rw [← eval_map_algebraMap]
    exact hβ
  · rw [hPdeg, residueDegree_eq_finrank, ← IntermediateField.adjoin.finrank hbi, hb,
      IntermediateField.finrank_top']
  · rw [hPmap]
    exact hsep
  · rw [hres]
    exact hb

theorem residueDegree_eq_one_iff_surjective (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L]
    [FiniteDimensional F L] :
    residueDegree F L = 1 ↔ Function.Surjective (algebraMap 𝓀[F] 𝓀[L]) := by
  rw [residueDegree_eq_finrank, ← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  constructor
  · intro h y
    have : y ∈ (⊥ : Subalgebra 𝓀[F] 𝓀[L]) := h ▸ Algebra.mem_top
    exact Algebra.mem_bot.1 this
  · intro h
    refine eq_top_iff.2 fun y _ ↦ Algebra.mem_bot.2 (h y)

theorem exists_unramified_adjoin :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnramified K K⟮(β : L)⟯ ∧ Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧
      residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hdeg, hsep, hgen⟩ := exists_lift_primitive K L
  set T := K⟮(β : L)⟯ with hT
  have hβL : aeval (β : L) P = 0 := by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) β P
    rw [hβ, map_zero] at this
    exact this
  have hle : Module.finrank K T ≤ residueDegree K L := by
    have hi : IsIntegral K (β : L) := .of_finite K _
    rw [hT, IntermediateField.adjoin.finrank hi, ← hdeg]
    have hne : P.map (algebraMap 𝒪[K] K) ≠ 0 := (hPm.map _).ne_zero
    have hd := minpoly.dvd K (β : L) (p := P.map (algebraMap 𝒪[K] K))
      (by rw [aeval_map_algebraMap]; exact hβL)
    calc (minpoly K (β : L)).natDegree ≤ (P.map (algebraMap 𝒪[K] K)).natDegree :=
          natDegree_le_of_dvd hd hne
      _ = P.natDegree := hPm.natDegree_map _
  have hβT : (β : L) ∈ T := IntermediateField.mem_adjoin_simple_self K _
  let βT : 𝒪[T] := ⟨⟨β, hβT⟩, (algebraMap_mem_integer_iff T L _).1 β.2⟩
  have hsurj : Function.Surjective (algebraMap 𝓀[T] 𝓀[L]) := by
    have := isScalarTower_residueField K T L (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    have hb : residue 𝒪[L] β ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range :=
      ⟨residue 𝒪[T] βT, rfl⟩
    have htop : Algebra.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hgen, IntermediateField.top_toSubalgebra]
    have hr : (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range = ⊤ :=
      eq_top_iff.2 (htop ▸ Algebra.adjoin_le (Set.singleton_subset_iff.2 hb))
    intro y
    obtain ⟨z, hz⟩ := (hr ▸ Algebra.mem_top : y ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range)
    exact ⟨z, hz⟩
  have h1 : residueDegree T L = 1 := (residueDegree_eq_one_iff_surjective L T).2 hsurj
  have htower := residueDegree_tower K T L
  rw [h1, mul_one] at htower
  have hfe : residueDegree K T ≤ Module.finrank K T := by
    rw [← ramificationIndex_mul_residueDegree K T]
    exact Nat.le_mul_of_pos_left _ (ramificationIndex_pos K T)
  have heq : Module.finrank K T = residueDegree K T := by omega
  exact ⟨β, P, hPm, hβ, hsep, (isUnramified_iff_residueDegree_eq_finrank K T).2 heq.symm,
    heq.trans htower.symm, h1⟩

theorem mem_of_residueDegree_eq_one (F : IntermediateField K L) (hF : residueDegree F L = 1)
    (P : 𝒪[K][X]) (hP : P.Monic) (γ : 𝒪[L]) (hγ : aeval γ P = 0)
    (hd : IsUnit (aeval γ (derivative P))) : (γ : L) ∈ F := by
  have hsurj := (residueDegree_eq_one_iff_surjective L F).1 hF
  have hinj : Function.Injective (algebraMap 𝓀[F] 𝓀[L]) := (algebraMap 𝓀[F] 𝓀[L]).injective
  obtain ⟨c₀', hc₀'⟩ := hsurj (residue 𝒪[L] γ)
  obtain ⟨c₀, rfl⟩ := residue_surjective (R := 𝒪[F]) c₀'
  have hc₀ : residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] c₀) = residue 𝒪[L] γ := hc₀'

  have key : ∀ Q : 𝒪[K][X], algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
      residue 𝒪[L] (aeval γ Q) := by
    intro Q
    rw [show algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
        residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] (aeval c₀ Q)) from rfl, ← aeval_algebraMap_apply,
      residue_aeval K L (fun _ ↦ rfl), hc₀, ← residue_aeval K L (fun _ ↦ rfl)]
  let Q := P.map (algebraMap 𝒪[K] 𝒪[F])
  have h1 : Q.eval c₀ ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap]
    apply hinj
    rw [key, hγ, map_zero, map_zero]
  have h2 : IsUnit (Q.derivative.eval c₀) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap]
    intro h0
    have := key (derivative P)
    rw [h0, map_zero] at this
    exact (residue_ne_zero_iff_isUnit _).2 hd this.symm
  obtain ⟨c, hc, hcc₀⟩ := HenselianLocalRing.is_henselian Q (hP.map _) c₀ h1 h2
  have hcF : aeval c P = 0 := by
    rw [← eval_map_algebraMap]
    exact hc
  set c' := algebraMap 𝒪[F] 𝒪[L] c
  have hc' : aeval c' P = 0 := by
    rw [aeval_algebraMap_apply, hcF, map_zero]
  have hres : residue 𝒪[L] c' = residue 𝒪[L] γ := by
    rw [← hc₀]
    have : residue 𝒪[F] c = residue 𝒪[F] c₀ := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hcc₀
    change algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c) = algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c₀)
    rw [this]
  have heq : γ = c' := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact hc') ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [heq]
  exact (c : F).2

end Extension

end GroundTheory.LocalField
