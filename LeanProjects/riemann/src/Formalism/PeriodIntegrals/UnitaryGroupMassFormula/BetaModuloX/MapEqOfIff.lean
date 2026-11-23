import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.HQTracePos

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem map_eq_of_iff (γ : S.V ≃ₗ[E] S.V) {U : Submodule E S.V} (h : ∀ v, γ v ∈ U ↔ v ∈ U) :
    U.map (γ : S.V →ₗ[E] S.V) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (h w).2 hw
  · intro hv
    refine ⟨γ.symm v, (h _).1 ?_, by simp⟩
    simpa using hv

theorem orth_iff {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (v : S.V) : γ v ∈ Uo F' ↔ v ∈ Uo F' := by
  simp only [Uo, mem_orth']
  constructor
  · intro h x hx
    have h1 := h (γ x) ((hX x).2 hx)
    rwa [hiso] at h1
  · intro h x hx
    have hx' : γ.symm x ∈ Xsp F' := (hX _).1 (by simpa using hx)
    have h1 := h _ hx'
    rwa [← hiso, LinearEquiv.apply_symm_apply] at h1

def γU {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') :
    Uo F' ≃ₗ[E] Uo F' :=
  γ.ofSubmodules _ _ (map_eq_of_iff γ hU)

theorem γU_coe {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (a : Uo F') : (γU F' γ hU a : S.V) = γ a := rfl

theorem γU_symm_coe {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (a : Uo F') : (((γU F' γ hU).symm a : Uo F') : S.V) = γ.symm a := by
  first
    | exact LinearEquiv.ofSubmodules_symm_apply _
    | simp [γU]

def γQ {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') : Qt F' ≃ₗ[E] Qt F' :=
  Submodule.Quotient.equiv (Pk F') (Pk F') (γU F' γ hU) (by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      show γ (b : S.V) ∈ Xsp F'
      exact (hX _).2 hb
    · intro ha
      refine ⟨(γU F' γ hU).symm a, ?_, by simp⟩
      show (((γU F' γ hU).symm a : Uo F') : S.V) ∈ Xsp F'
      rw [γU_symm_coe]
      apply (hX _).1
      rw [LinearEquiv.apply_symm_apply]
      exact ha)

theorem γQ_mk {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (a : Uo F') :
    γQ F' γ hU hX (Submodule.Quotient.mk a) = Submodule.Quotient.mk (γU F' γ hU a) := rfl

theorem γQ_isom {T' : E} (F' : LFlag S r T') (γ : S.V ≃ₗ[E] S.V) (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F')
    (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (hz : γ F'.fl.z = F'.fl.z) (c : E) : γQ F' γ hU hX ∈ Formalism.HermitianLatticesTheory.isom (hQ F' c) := by
  show ∀ x y, (hQ F' c) ((γQ F' γ hU hX) x) ((γQ F' γ hU hX) y) = (hQ F' c) x y
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H a =>
  induction y using Submodule.Quotient.induction_on with
  | H b =>
  rw [γQ_mk, γQ_mk, hQ_mk, hQ_mk, hV_apply, hV_apply, γU_coe, γU_coe]
  conv_lhs => rw [← hz]
  simp only [hiso]

def ΛU {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Uo F') :=
  Λ.comap ((Uo F').subtype.restrictScalars (𝓞 E))

def Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Qt F') :=
  (ΛU F' Λ).map ((Pk F').mkQ.restrictScalars (𝓞 E))

theorem mem_Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) {q : Qt F'} :
    q ∈ Lb F' Λ ↔ ∃ a : Uo F', (a : S.V) ∈ Λ ∧ Submodule.Quotient.mk a = q := by
  first
    | exact Iff.rfl
    | (simp [Lb, ΛU]; done)
    | (constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩)

theorem Lb_lattice {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Lb F' Λ) := by
  refine ⟨?_, ?_⟩
  · have hfg : Λ.FG := hΛ.fg
    have hN : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hfg
    have h1 : (ΛU F' Λ).FG := by
      apply Submodule.fg_of_fg_map_injective ((Uo F').subtype.restrictScalars (𝓞 E)) Subtype.val_injective
      have hle : (ΛU F' Λ).map ((Uo F').subtype.restrictScalars (𝓞 E)) ≤ Λ := by
        rintro _ ⟨a, ha, rfl⟩
        exact ha
      exact (isNoetherian_submodule.1 hN) _ hle
    exact h1.map _
  · rw [eq_top_iff]
    intro q _
    induction q using Submodule.Quotient.induction_on with
    | H a =>
      obtain ⟨o, ho, hoa⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ hΛ (a : S.V)
      have hmem : (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') ∈ Lb F' Λ :=
        (mem_Lb F' Λ).2 ⟨o • a, by simpa using hoa, rfl⟩
      have ho' : (algebraMap (𝓞 E) E o) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
      have : (Submodule.Quotient.mk (p := Pk F') a : Qt F') =
          (algebraMap (𝓞 E) E o)⁻¹ • (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') := by
        rw [Submodule.Quotient.mk_smul, ← algebraMap_smul E o, smul_smul, inv_mul_cancel₀ ho', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem γQ_Lb {T' : E} (F' : LFlag S r T') (Λ : Submodule (𝓞 E) S.V) (γ : S.V ≃ₗ[E] S.V)
    (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F') (hA : IsAutLam S Λ γ) :
    Formalism.HermitianLatticesTheory.gmap (γQ F' γ hU hX) (Lb F' Λ) = Lb F' Λ := by
  have hA2 : Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hA.2
  unfold Formalism.HermitianLatticesTheory.gmap
  apply le_antisymm
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hq0
    refine (mem_Lb F' Λ).2 ⟨γU F' γ hU a, ?_, rfl⟩
    rw [γU_coe]
    have h1 : γ (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) := ⟨a, ha, rfl⟩
    rwa [hA2] at h1
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hq
    have h1 : (a : S.V) ∈ Λ.map ((γ : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) := by
      rw [hA2]
      exact ha
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.1 h1
    have hba' : γ b = (a : S.V) := hba
    have hbU : b ∈ Uo F' := (hU b).1 (by rw [hba']; exact a.2)
    refine Submodule.mem_map.2 ⟨Submodule.Quotient.mk ⟨b, hbU⟩, (mem_Lb F' Λ).2 ⟨⟨b, hbU⟩, hb, rfl⟩, ?_⟩
    show γQ F' γ hU hX (Submodule.Quotient.mk ⟨b, hbU⟩) = Submodule.Quotient.mk a
    rw [γQ_mk]
    congr 1
    ext
    rw [γU_coe]
    exact hba'

theorem gmap_mul' {T' : E} (F' : LFlag S r T') (a b : Qt F' ≃ₗ[E] Qt F') (L : Submodule (𝓞 E) (Qt F')) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  first
    | rfl
    | (congr 1)

theorem γQ_finOrd {T' : ℕ} (F' : LFlag S r ((T' : ℕ) : E)) (hT : 0 < T')
    (hτ : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hpos : ∀ τ : E →+* ℂ, ∀ w ∈ orth S (Xplus F'), w ∉ Xsp F' → 0 < (τ (S.hT w w)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (γ : S.V ≃ₗ[E] S.V) (hA : IsAutLam S Λ γ)
    (hU : ∀ v, γ v ∈ Uo F' ↔ v ∈ Uo F') (hX : ∀ v, γ v ∈ Xsp F' ↔ v ∈ Xsp F')
    (hz : γ F'.fl.z = F'.fl.z) :
    ∃ n : ℕ, 0 < n ∧ γQ F' γ hU hX ^ n = 1 := by
  have hc : star (2 / ((T' : ℕ) : E)) = 2 / ((T' : ℕ) : E) := by
    rw [star_div₀, star_natCast, star_ofNat]
  have hfin := Formalism.HermitianLatticesTheory.autFinite E (Qt F') (hQ F' (2 / ((T' : ℕ) : E))) (hQ_symm F' _ hc)
    (hQ_trace_pos F' hT hτ hpos) (Lb F' Λ) (Lb_lattice F' Λ hΛ)
  have hmem : ∀ k : ℕ, γQ F' γ hU hX ^ k ∈ {g | g ∈ Formalism.HermitianLatticesTheory.isom (hQ F' (2 / ((T' : ℕ) : E))) ∧
      Formalism.HermitianLatticesTheory.gmap g (Lb F' Λ) = Lb F' Λ} := by
    intro k
    induction k with
    | zero =>
      refine ⟨Subgroup.one_mem _, ?_⟩
      unfold Formalism.HermitianLatticesTheory.gmap
      ext q
      simp
    | succ k ih =>
      refine ⟨Subgroup.pow_mem _ (γQ_isom F' γ hU hX hA.1 hz _) _, ?_⟩
      rw [pow_succ, gmap_mul', γQ_Lb F' Λ γ hU hX hA, ih.2]
  obtain ⟨m, n, hmn, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  have h1 : γQ F' γ hU hX ^ m * γQ F' γ hU hX ^ (n - m) = γQ F' γ hU hX ^ m * 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hmn.le, mul_one, he]
  exact mul_left_cancel h1

end Q3

end PI.UnitaryGroupMassFormula.BetaModX
