import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section LevelIndex

variable {R : Type} [Ring R] {L : Type} [AddCommGroup L] [Module R L]

def multiplesSub (L : Type) [AddCommGroup L] (N : ℕ) : AddSubgroup L := (nsmulAddMonoidHom (α := L) N).range

theorem finite_quot_multiplesSub [Module.Finite ℤ L] {N : ℕ} (hN : 0 < N) :
    Finite (L ⧸ multiplesSub L N) := by
  have : Module.Finite ℤ (L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) := inferInstance
  have htors : Module.IsTorsion ℤ (L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) := by
    intro x
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show (N : ℤ) • (Submodule.Quotient.mk y : L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  exact Module.finite_of_fg_torsion (M := L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) htors

def modAct (N : ℕ) : (L ≃ₗ[R] L) →* Function.End (L ⧸ multiplesSub L N) where
  toFun γ := ⇑(QuotientAddGroup.map (multiplesSub L N) (multiplesSub L N)
    (γ.toLinearMap.toAddMonoidHom) (by
      rintro _ ⟨e, rfl⟩
      exact ⟨γ e, by simp⟩))
  map_one' := by
    funext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rfl
  map_mul' a b := by
    funext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rfl

theorem modAct_mk (N : ℕ) (γ : L ≃ₗ[R] L) (a : L) :
    modAct N γ (a : L ⧸ multiplesSub L N) = ((γ a : L) : L ⧸ multiplesSub L N) := rfl

def modKer (R : Type) [Ring R] (L : Type) [AddCommGroup L] [Module R L] (N : ℕ) : Subgroup (L ≃ₗ[R] L) :=
  (modAct (R := R) (L := L) N).toHomUnits.ker

theorem modKer_finiteIndex [Module.Finite ℤ L] {N : ℕ} (hN : 0 < N) :
    (modKer R L N).FiniteIndex := by
  have := finite_quot_multiplesSub (L := L) hN
  have : Finite (Function.End (L ⧸ multiplesSub L N)) := inferInstanceAs (Finite (_ → _))
  exact Subgroup.finiteIndex_ker _

theorem exists_of_mem_modKer {N : ℕ} {γ : L ≃ₗ[R] L} (h : γ ∈ modKer R L N) (a : L) :
    ∃ e, γ a = a + N • e := by
  have h1 : modAct N γ = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.1 h)
    simpa using this
  have h2 := congrFun h1 (a : L ⧸ multiplesSub L N)
  rw [modAct_mk] at h2
  have h3 : ((γ a : L) : L ⧸ multiplesSub L N) = (a : L ⧸ multiplesSub L N) := h2
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 h3.symm
  refine ⟨e, ?_⟩
  have he' : N • e = -a + γ a := he
  rw [he']
  abel

end LevelIndex

def levelGrp {E : Type} [Field E] [NumberField E] {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | (∀ a b, form (γ a) (γ b) = form a b) ∧
    (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e}
  one_mem' := ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩
    · show form (γ (δ a)) (γ (δ b)) = form a b
      rw [h1, k1]
    · obtain ⟨e, he⟩ := k2 a ha
      obtain ⟨e', he'⟩ := h2 a ha
      refine ⟨e' + γ e, ?_⟩
      show γ (δ a) = _
      rw [he, map_add, he', map_nsmul, smul_add, add_assoc]
    · obtain ⟨e, he⟩ := k3 a
      obtain ⟨e', he'⟩ := h3 a
      refine ⟨e' + γ e, ?_⟩
      show γ (δ a) = _
      rw [he, map_add, he', map_nsmul, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨h1, h2, h3⟩
    have hinv : ∀ a, γ (γ⁻¹ a) = a := fun a => γ.apply_symm_apply a
    refine ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩
    · have := h1 (γ⁻¹ a) (γ⁻¹ b)
      rw [hinv, hinv] at this
      exact this.symm
    · have hmem : γ⁻¹ a ∈ I • (⊤ : Submodule (𝓞 E) Λ) := by
        refine Submodule.smul_induction_on ha ?_ ?_
        · intro r hr n _
          rw [map_smul]
          exact Submodule.smul_mem_smul hr trivial
        · intro x y hx hy
          rw [map_add]
          exact add_mem hx hy
      obtain ⟨e, he⟩ := h2 _ hmem
      rw [hinv] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg]
      exact eq_add_neg_of_add_eq he.symm
    · obtain ⟨e, he⟩ := h3 (γ⁻¹ a)
      rw [hinv] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg]
      exact eq_add_neg_of_add_eq he.symm

theorem levelGrp_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite ℤ Λ] (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ), 0 < M → 0 < A → ∃ Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ), Γ ≤ autGrp form ∧ Γ.relIndex (autGrp form) ≠ 0 ∧ ∀ γ, γ ∈ Γ ↔ (∀ a b, form (γ a) (γ b) = form a b) ∧ (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e := by
  intro E _ _ _ Λ _ _ _ form I M A hM hA
  refine ⟨levelGrp form I M A, fun γ h => h.1, ?_, fun γ => Iff.rfl⟩
  have hfin := modKer_finiteIndex (R := 𝓞 E) (L := Λ) (Nat.mul_pos hM hA)
  have hle : modKer (𝓞 E) Λ (M * A) ⊓ autGrp form ≤ levelGrp form I M A := by
    rintro γ ⟨hk, ha⟩
    refine ⟨ha, fun a _ => ?_, fun a => ?_⟩
    · obtain ⟨e, he⟩ := exists_of_mem_modKer hk a
      exact ⟨A • e, by rw [he, mul_smul]⟩
    · obtain ⟨e, he⟩ := exists_of_mem_modKer hk a
      exact ⟨M • e, by rw [he, mul_comm, mul_smul]⟩
  have h0 : (modKer (𝓞 E) Λ (M * A) ⊓ autGrp form).relIndex (autGrp form) ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  intro h
  have hd := Subgroup.relIndex_dvd_of_le_left (autGrp form) hle
  rw [h] at hd
  exact h0 (Nat.eq_zero_of_zero_dvd hd)

end GlobalTheory.CompanionTheory.Ar.Cusp
