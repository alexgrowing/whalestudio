import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.HalfReps

section Group

variable {H : Type} [AddCommGroup H] [Module ℚ H] [Module.Finite ℚ H]

theorem relIndex_nsmul (Λ : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c) :
    (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≠ 0 ∧
      (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≤ c ^ Module.finrank ℚ H := by
  have : IsAddTorsionFree H := IsAddTorsionFree.of_module_rat H
  have : Module.Finite ℤ Λ.toIntSubmodule := hΛ
  have : Module.Free ℤ Λ.toIntSubmodule := inferInstance
  rw [AddSubgroup.relIndex_map_nsmul]
  refine ⟨pow_ne_zero _ hc.ne', Nat.pow_le_pow_right hc ?_⟩
  have hb := (Module.finBasis ℤ Λ.toIntSubmodule).linearIndependent.map' Λ.toIntSubmodule.subtype
    (Submodule.ker_subtype _)
  have := ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hb).fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem relIndex_of_nsmul_le (Λ B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ B, c • x ∈ Λ) : Λ.relIndex B ≠ 0 ∧ Λ.relIndex B ≤ c ^ Module.finrank ℚ H := by
  have : IsAddTorsionFree H := IsAddTorsionFree.of_module_rat H
  obtain ⟨h0, h1⟩ := relIndex_nsmul Λ hΛ hc
  have hle : B.map (nsmulAddMonoidHom c) ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := nsmulAddMonoidHom c) Λ B (nsmul_right_injective hc.ne')]
  exact ⟨fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_right hle h),
    (AddSubgroup.relIndex_le_of_le_right hle h0).trans h1⟩

theorem relIndex_of_le_nsmul (Λ A B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ Λ, c • x ∈ B) : B.relIndex (Λ ⊓ A) ≠ 0 := by
  obtain ⟨h0, -⟩ := relIndex_nsmul Λ hΛ hc
  have hle : Λ.map (nsmulAddMonoidHom c) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle
    (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h))

end Group

section Twist

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem nsmul_mem_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, e Q ≤ 1) {x : W} (hx : x ∈ M) : c • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine (mem_twO M c e _).2 fun Q => GlobalTheory.ThetaMove.mem_localization_of_mem Q ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 - e Q by have := he Q; omega)
  have : ((c : E) ^ e Q)⁻¹ • c • x = (c ^ m) • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_sub₀ hcE, zpow_one, div_eq_inv_mul]
  rw [this]
  exact nsmul_mem hx _

theorem nsmul_mem_of_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, -1 ≤ e Q) {x : W} (hx : x ∈ twist₂ M c e) : c • x ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 + e Q by have := he Q; omega)
  have : c • x = (c ^ m) • ((c : E) ^ e Q)⁻¹ • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_add₀ hcE, zpow_one, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hcE), mul_one]
  rw [this]
  exact nsmul_mem ((mem_twO M c e x).1 hx Q) _

end Twist

theorem half_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (dl : ℂ) (AA : Submodule (𝓞 E) E) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (c : ℕ), dl ≠ 0 → AA.FG → Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < c → Formalism.L2.Th1.H.IsReps (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c) (repsOf (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c)) ∧ Formalism.L2.Th1.H.IsReps (LamC emb dl AA L L') (BC emb dl AA S L L' c) (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)) ∧ (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)).card ≤ c ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ ι _ _ a b emb dl AA S L L' c hdl hA hL hL' hc
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := a) (b := b) emb hdl
  have hfg : (perO AA L L').FG :=
    GlobalTheory.ThetaMove.VolumePos.perO_fg hA (GlobalTheory.ThetaMove.VolumePos.homO_fg hL.fg hL'.fg hL.span_eq_top)
  have : Module.Finite (𝓞 E) (perO AA L L') := Module.Finite.iff_fg.2 hfg
  have hfin : Module.Finite ℤ (perO AA L L') := Module.Finite.trans (𝓞 E) _
  have : Module.Finite ℚ (Formalism.L2.Col.HomE E a b) := Module.Finite.trans E _
  have hrk : Module.finrank ℚ (Formalism.L2.Col.HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E, Module.finrank_linearMap]
    simp [mul_assoc]
  have h1 := relIndex_of_le_nsmul (perO AA L L').toAddSubgroup (halfAO S (perO AA L L') c).toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).2) hx)
  have h2 := relIndex_of_nsmul_le (perO AA L L').toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_of_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).1) hx)
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf _ _ _ hinj] at h1
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hrk] at h2
  have r2 := Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h2.1)
  refine ⟨Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h1), r2, ?_⟩
  exact (GlobalTheory.RepsMod.card_reps _ _ _ r2).le.trans h2.2

end GlobalTheory.ColNorms.HalfReps
