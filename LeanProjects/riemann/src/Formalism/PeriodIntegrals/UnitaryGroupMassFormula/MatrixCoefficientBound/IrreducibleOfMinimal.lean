import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.RepresentationDimensionPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section Irr

variable {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem irreducible_of_minimal (π : Representation ℂ G V) (W : Subrepresentation π) (hW : W ≠ ⊥)
    (hmin : ∀ W' : Subrepresentation π, W' ≠ ⊥ → W' ≤ W →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ W'.toSubmodule) :
    W.toRepresentation.IsIrreducible := by
  have hWs : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial (Subrepresentation W.toRepresentation) := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWs
    refine ⟨⟨⊥, ⊤, fun h => hx0 ?_⟩⟩
    have hmem : (⟨x, hxW⟩ : W.toSubmodule) ∈ (⊤ : Subrepresentation W.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← h] at hmem
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hmem)
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hSs : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let S' : Subrepresentation π := ⟨S.toSubmodule.map W.toSubmodule.subtype, by
    rintro g _ ⟨y, hy, rfl⟩
    exact ⟨W.toRepresentation g y, S.apply_mem_toSubmodule g hy, rfl⟩⟩
  have hS'0 : S' ≠ ⊥ := by
    obtain ⟨y, hyS, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSs
    intro h
    have hmem : (y : V) ∈ S'.toSubmodule := ⟨y, hyS, rfl⟩
    rw [h] at hmem
    exact hy0 (Subtype.ext ((Submodule.mem_bot ℂ).mp hmem))
  have hle : S' ≤ W := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hrank := hmin S' hS'0 hle
  have e1 : Module.finrank ℂ S'.toSubmodule = Module.finrank ℂ S.toSubmodule :=
    (Submodule.equivMapOfInjective _ W.toSubmodule.injective_subtype S.toSubmodule).finrank_eq.symm
  have htop : S.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq (by
    have := Submodule.finrank_le S.toSubmodule
    omega)
  exact Subrepresentation.toSubmodule_injective htop

theorem exists_irreducible_le (π : Representation ℂ G V) (E : Subrepresentation π) (hE : E ≠ ⊥) :
    ∃ W : Subrepresentation π, W ≠ ⊥ ∧ W ≤ E ∧ W.toRepresentation.IsIrreducible := by
  have hex : ∃ d, ∃ W : Subrepresentation π, W ≠ ⊥ ∧ W ≤ E ∧ Module.finrank ℂ W.toSubmodule = d :=
    ⟨_, E, hE, le_rfl, rfl⟩
  obtain ⟨W, hW, hWE, hWd⟩ := Nat.find_spec hex
  refine ⟨W, hW, hWE, irreducible_of_minimal π W hW fun W' hW' hW'W => ?_⟩
  rw [hWd]
  exact Nat.find_min' hex ⟨W', hW', hW'W.trans hWE, rfl⟩

end Irr

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem repGam_subrep {V : Type} [AddCommGroup V] [Module ℂ V] (ψ₀ : AddChar F ℂ)
    (π : Representation ℂ (GL (Fin k) F) V) (W : Subrepresentation π) (u : W.toSubmodule) :
    ((repGam ψ₀ W.toRepresentation u : W.toSubmodule) : V) = repGam ψ₀ π (u : V) := by
  simp only [repGam, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  first
    | rfl
    | simp

theorem gam_one_real (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (((Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) : ℝ) : ℂ) := by
  have hsd : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
    unfold superdiag
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro hij
      subst hij
      omega
    · rfl
  have hpsi : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    unfold psiNat psiU
    rw [if_pos isUni_one, Units.val_one, hsd, AddChar.map_zero_eq_one]
  unfold gam
  have h1 : ∀ y : GL (Fin k) F, y * 1 * y⁻¹ = 1 := fun y => by group
  have h2 : ∀ y : GL (Fin k) F, y * y⁻¹ = 1 := fun y => by group
  simp only [h1, h2, hpsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem gam_one_re_pos (ψ₀ : AddChar F ℂ) : 0 < (gam ψ₀ (1 : GL (Fin k) F)).re := by
  rw [gam_one_real, Complex.ofReal_re]
  have hU : 0 < cardU F k := by
    unfold cardU
    haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, isUni_one⟩⟩
    exact Nat.card_pos
  have hG : 0 < Fintype.card (GL (Fin k) F) := Fintype.card_pos
  exact div_pos (by exact_mod_cast hG) (by exact_mod_cast hU)

theorem eig_place (hC : ConvScalar) (hR : GenericRatio) (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1)
    (hq : 3 ≤ Fintype.card F) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (c : ℂ) (w : V) (hw : w ≠ 0)
    (hc : repGam ψ₀ π w = c • w) :
    ∃ r : ℝ, c = r ∧ 0 ≤ r ∧
      r ≤ (gam ψ₀ (1 : GL (Fin k) F)).re * (1 + 3 / (Fintype.card F : ℝ)) := by
  have hcomm := PI.GGConvScalarW.representation_commutes_gamma F k ψ₀ V π
  let E : Subrepresentation π := ⟨LinearMap.ker (repGam ψ₀ π - c • LinearMap.id), by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hv ⊢
    have h1 := congrArg (fun f => f v) (hcomm g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hv, map_smul]⟩
  have hmemE : ∀ v, v ∈ E.toSubmodule ↔ repGam ψ₀ π v = c • v := by
    intro v
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hE : E ≠ ⊥ := by
    intro h
    have hwE : w ∈ E.toSubmodule := (hmemE w).mpr hc
    rw [h] at hwE
    exact hw ((Submodule.mem_bot ℂ).mp hwE)
  obtain ⟨W, hW0, hWE, hirr⟩ := exists_irreducible_le π E hE
  have hWs : W.toSubmodule ≠ ⊥ := fun h => hW0 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWs
  have hu_eig : repGam ψ₀ π u = c • u := (hmemE u).mp (hWE huW)
  have hpos := gam_one_re_pos (k := k) ψ₀
  have hg1 : gam ψ₀ (1 : GL (Fin k) F) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hCS := hC F k ψ₀ hψ W.toSubmodule W.toRepresentation hirr
  have hrep : repGam ψ₀ W.toRepresentation =
      gam ψ₀ (1 : GL (Fin k) F) • ((gam ψ₀ (1 : GL (Fin k) F))⁻¹ • repGam ψ₀ W.toRepresentation) := by
    rw [smul_smul, mul_inv_cancel₀ hg1, one_smul]
  rw [hCS] at hrep
  have k0 := repGam_subrep ψ₀ π W ⟨u, huW⟩
  rw [hrep, hu_eig] at k0
  have hreal := gam_one_real (k := k) ψ₀
  have hre : (gam ψ₀ (1 : GL (Fin k) F)).re =
      (Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) := by
    rw [hreal, Complex.ofReal_re]
  by_cases hgen : Generic ψ₀ W.toRepresentation
  · rw [if_pos hgen] at k0
    have k1 : (gam ψ₀ (1 : GL (Fin k) F) *
        ((cardU F k : ℂ) / (Module.finrank ℂ W.toSubmodule : ℂ))) • u = c • u := by
      rw [← k0, mul_smul]
      rfl
    have hc_eq : c = gam ψ₀ (1 : GL (Fin k) F) *
        ((cardU F k : ℂ) / (Module.finrank ℂ W.toSubmodule : ℂ)) :=
      (smul_left_injective ℂ hu0 k1).symm
    refine ⟨(Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) *
      ((cardU F k : ℝ) / (Module.finrank ℂ W.toSubmodule : ℝ)), ?_, by positivity, ?_⟩
    · rw [hc_eq, hreal]
      push_cast
      ring
    · rw [hre]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hR F k ψ₀ hψ W.toSubmodule W.toRepresentation hirr hgen).trans
        (ratio_numeric k _ (by exact_mod_cast hq))
  · rw [if_neg hgen, smul_zero] at k0
    have hcu : c • u = 0 := by
      rw [← k0]
      rfl
    refine ⟨0, ?_, le_rfl, ?_⟩
    · rcases smul_eq_zero.mp hcu with h | h
      · rw [h, Complex.ofReal_zero]
      · exact absurd h hu0
    · rw [hre]
      positivity

theorem local_place_bound : PlaceBound := by
  intro hC hR F _ _ k ψ₀ hψ hq V _ _ _ π W μ hW _ hμ
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨r, hr, hr0, hr1⟩ := eig_place hC hR ψ₀ hψ hq π μ w hw0 (hμ w hwW)
  have hpos := gam_one_re_pos (k := k) ψ₀
  set g := (gam ψ₀ (1 : GL (Fin k) F)).re with hg
  have hg0 : g ≠ 0 := hpos.ne'
  have hgam : gam ψ₀ (1 : GL (Fin k) F) = (g : ℂ) := by
    rw [hg, gam_one_real, Complex.ofReal_re]
  refine ⟨r / g, ?_, div_nonneg hr0 hpos.le, ?_⟩
  · rw [hr, hgam, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · first
      | (rw [div_le_iff₀ hpos]; linarith)
      | (rw [div_le_iff hpos]; linarith)

end PI.GGMatBoundW
