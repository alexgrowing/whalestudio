import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatOpenCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix Pointwise

variable {D : D7} (X : HidaSetting D)

def eC : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F := 1 - X.ew - sigA X.B.I X.ew

theorem imA_eC_idem : eC X * eC X = eC X := by
  have h1 := X.ew_idem
  have h2 := X.ew_orth
  have h3 : sigA X.B.I X.ew * sigA X.B.I X.ew = sigA X.B.I X.ew := by rw [← map_mul, h1]
  simp only [eC]
  linear_combination h1 + h3 + 2 * h2

theorem imA_mL_mem (m : ℕ) {b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hb' : b ∈ mL X.B.I m) : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
  induction hb' using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
  | smul c y _ hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
    show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
    rw [smul_smul, smul_smul, mul_comm]

theorem imA_lat_fg (p : TypX X) : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).FG := by
  classical
  obtain ⟨m, b, hb', -, he⟩ := MassDataIdxK.latImage p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg
  refine ⟨(Finset.univ.image b), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hb' i
  · intro x hx
    have hx' : x ∈ (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
        Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) := hx
    rw [he] at hx'
    obtain ⟨c, hc, rfl⟩ := hx'
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i • b i = (⟨c i, hc i (Set.mem_univ _)⟩ : p.1.adicCompletionIntegers X.B.I.F) • b i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem imA_g_nonunit (p : TypX X) : ¬ IsUnit ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  intro hu
  obtain ⟨π, -, -⟩ := stResZ_holds X p
  have hd : gOf p ∣ X.B.g := by
    rw [X.g_eq]; unfold gOf; split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hu' : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hu
  have h0 : π ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have h1 := hu'.map π
  rw [h0] at h1
  exact not_isUnit_zero h1

theorem imA_n_pos : 0 < X.B.I.n := by
  rw [X.n_eq]
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem imA_ew_split (p : TypX X) :
    PI.FinKW.psiV X.B.I p.1 X.ew + PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) = 1 := by
  set ε := PI.FinKW.psiV X.B.I p.1 (eC X) with hε
  have hεi : ε * ε = ε := by rw [hε, ← map_mul, imA_eC_idem]
  let φ : (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) →ₗ[p.1.adicCompletionIntegers X.B.I.F]
      (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
    { toFun := fun u => ε • u
      map_add' := fun u w => smul_add _ _ _
      map_smul' := fun c u => smul_comm _ _ _ }
  have hφ : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    show ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l ∈
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := imA_mL_mem X X.B.g (X.ew_full _ hin)
    have hv : PI.FinKW.vecV X.B.I p.1 (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l := by
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    have h2 := congrArg (PI.FinKW.vecV X.B.I p.1) he
    rw [imA_vecV_smul', imA_vecV_smul', hv, map_natCast] at h2
    have h3 : ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l =
        ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) • PI.FinKW.vecV X.B.I p.1 y := by
      rw [Nat.cast_smul_eq_nsmul] at h2
      rw [hε, Nat.cast_smul_eq_nsmul]
      exact h2
    rw [h3]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy p.1)
  have hφφ : φ.comp φ = φ := LinearMap.ext fun u => by
    show ε • ε • u = ε • u
    rw [smul_smul, hεi]
  have hN : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ := by
    calc _ = ((latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ).map φ := by
            rw [← Submodule.map_comp, hφφ]
      _ ≤ _ := Submodule.map_mono hφ
      _ = _ := Submodule.map_smul'' _ _ _
  have hjac : Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (imA_g_nonunit X p)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ ((imA_lat_fg X p).map φ) hN hjac
  have hz : ∀ l ∈ X.B.I.L, ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l = 0 := by
    intro l hl
    have : φ (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l) ∈
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, hl, rfl⟩)
    rw [hbot] at this
    exact this
  have hex : ∃ l ∈ X.B.I.L, l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hs := X.B.I.L_span
    rw [Submodule.span_eq_bot.mpr h] at hs
    have i0 : Fin X.B.I.n := ⟨0, imA_n_pos X⟩
    have hm : (Pi.single i0 (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ (⊥ : Submodule X.B.I.E _) := by
      rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hm
    have := congrFun hm i0
    simp at this
  obtain ⟨l, hl, hl0⟩ := hex
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hl0
  have h0 := congrFun (hz l hl) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hu : IsUnit (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l i) :=
    (isUnit_iff_ne_zero.mpr hi).map (inclR (F := X.B.I.F) (Fv X.B.I.F p.1))
  have hε0 : ε = 0 := (hu.mul_left_eq_zero).mp h0
  rw [hε, eC, map_sub, map_sub, map_one] at hε0
  linear_combination -hε0

end MassDataIdxSteps
