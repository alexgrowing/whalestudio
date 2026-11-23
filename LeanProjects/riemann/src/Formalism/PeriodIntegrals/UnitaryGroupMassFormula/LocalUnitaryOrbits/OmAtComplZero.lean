import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omAt_compl_zero {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    omAt σ J ψ v T {X | gramR (Fv F v) σ J X = T}ᶜ = 0 := by
  unfold omAt
  split_ifs with hT
  · unfold omFam
    split_ifs with hf
    · have h1 := (hf.choose_spec).1 ⟨T, hT⟩
      refine measure_mono_null (fun X hX => ?_) h1
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hX
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, not_and]
      intro h; exact absurd h hX
    · simp
  · simp

theorem smul_mem_LamT {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : Y ∈ LamT v Λ a) : k • Y ∈ LamT v Λ a := by
  intro i
  exact (hk (Y i)).1 (hY i)

theorem qv_pos : 0 < qv v := by
  unfold qv
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem absV_dV_pos : 0 < absV v (dV v) := by
  have hd : dV v ≠ 0 := by
    unfold dV; split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  unfold absV
  rw [dif_neg (by simpa using hd)]
  exact zpow_pos (qv_pos v) _

theorem omLocU_of (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  intro hS hL hSD hUn ha hP hdet
  have hG : GoodY σ J ψ v Λ a Y := ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩
  obtain ⟨ϖ, hϖ⟩ := hU
  obtain ⟨hW, hH⟩ := hSd hS
  set T := gramR (Fv F v) σ J Y with hTdef
  set ω := omAt σ J ψ v T with hω
  set O := {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} with hO

  have hYL : Y ∈ LamT v Λ a := hP.1
  have hsub : O ⊆ LamT v Λ a := by
    rintro X ⟨k, hk, rfl⟩; exact smul_mem_LamT σ J v Λ k hk Y hYL
  have hsup : LamT v Λ a ⊆ O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ := by
    intro X hX
    by_cases hg : gramR (Fv F v) σ J X = T
    · exact Or.inl (h1 hG X hX hg)
    · exact Or.inr hg
  have hEq : ω O = ω (LamT v Λ a) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (LamT v Λ a) ≤ ω (O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {X | gramR (Fv F v) σ J X = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero σ J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, h2 hG (hOm hS).1 ϖ hϖ, h3 hG hW ϖ hϖ, h4 hS hL hSD hUn hW, h5 hS hUn hH ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((n : ℝ) * a) / absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEta
  have : (0 : ℝ) < qv v ^ (-((a : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end PI.OmLocU
