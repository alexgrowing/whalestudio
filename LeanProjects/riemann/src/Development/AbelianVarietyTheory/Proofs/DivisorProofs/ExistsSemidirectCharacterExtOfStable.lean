import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSSRepOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyPowMulEqOneStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.StableExt

theorem isSSRep_of_finite {G : Type} [Group G] [Finite G] {d : ℕ} (ρ : G →* GL (Fin d) ℂ) :
    Formalism.MainNotions.N.IsSSRep ρ := by
  haveI : (⊥ : Subgroup G).FiniteIndex := inferInstance
  apply GlobalTheory.FiniteIndexSemisimple.isSSRep_of_finiteIndex ρ (⊥ : Subgroup G)
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hg, map_one, Units.val_one, Matrix.one_mulVec]
  exact hv

theorem commute_aeval {n : ℕ} {M B : Matrix (Fin n) (Fin n) ℂ} (h : Commute M B) (p : ℂ[X]) :
    Commute M (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem exists_ext : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) →
    ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  intro G Γ _ _ _ _ φ s hs Y hY hYs
  obtain ⟨d, ρ, hρ⟩ := (GlobalTheory.BI.matrixChar_iff_isChar G Y).mpr hY
  let ρ' : G →* GL (Fin d) ℂ := ρ.comp (φ s).toMonoidHom
  obtain ⟨A, hA⟩ := GlobalTheory.TraceConj.conj_of_trace_eq G ℂ d ρ ρ' (isSSRep_of_finite ρ)
    (isSSRep_of_finite ρ') (fun g => by
      show _ = Matrix.trace ((ρ (φ s g) : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      rw [← hρ, ← hρ, hYs])
  have hA' : ∀ g, ρ (φ s g) = A * ρ g * A⁻¹ := fun g => hA g
  have hAk : ∀ k : ℕ, ∀ g, ρ (((φ s) ^ k) g) = A ^ k * ρ g * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', MulAut.mul_apply, hA', ih]; group
  set l := orderOf s with hl_def
  have hl : 0 < l := orderOf_pos s
  have hφl : (φ s) ^ l = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hB : ∀ g, A ^ l * ρ g = ρ g * A ^ l := by
    intro g
    have := hAk l g
    rw [hφl, MulAut.one_apply] at this
    calc A ^ l * ρ g = (A ^ l * ρ g * (A ^ l)⁻¹) * A ^ l := by group
      _ = ρ g * A ^ l := by rw [← this]
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_poly_pow_mul_eq_one' d l ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) hl (Units.isUnit _)
  set Bm : Matrix (Fin d) (Fin d) ℂ := ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) with hBm
  set C : Matrix (Fin d) (Fin d) ℂ := aeval Bm p with hC
  have hCA : Commute ((A : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    apply commute_aeval
    rw [hBm, Units.val_pow_eq_pow_val]
    exact (Commute.refl _).pow_right l
  have hCρ : ∀ g, Commute ((ρ g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    intro g
    apply commute_aeval
    have := congrArg (fun x : GL (Fin d) ℂ => (x : Matrix (Fin d) (Fin d) ℂ)) (hB g)
    simp only [Units.val_mul] at this
    exact this.symm
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have h1 : C * (C ^ (l - 1) * Bm) = 1 := by
    rw [← mul_assoc, ← pow_succ', hl1]; exact hp
  let Cu : GL (Fin d) ℂ := ⟨C, C ^ (l - 1) * Bm, h1, mul_eq_one_comm.mp h1⟩
  have hCuA : A * Cu = Cu * A := Units.ext (hCA.eq)
  have hCuρ : ∀ g, Cu * ρ g = ρ g * Cu := fun g => Units.ext ((hCρ g).eq.symm)
  have hCuB : Cu ^ l * A ^ l = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]; exact hp)
  set A' : GL (Fin d) ℂ := A * Cu with hA'def
  have hA'l : A' ^ l = 1 := by
    rw [hA'def, (show Commute A Cu from hCuA).mul_pow, ((show Commute A Cu from hCuA).pow_pow l l).eq]
    exact hCuB
  have hA's : ∀ g, ρ (φ s g) = A' * ρ g * A'⁻¹ := by
    intro g
    rw [hA', hA'def, mul_inv_rev]
    calc A * ρ g * A⁻¹ = A * (ρ g * Cu) * Cu⁻¹ * A⁻¹ := by group
      _ = A * Cu * ρ g * (Cu⁻¹ * A⁻¹) := by rw [← hCuρ g]; group
  let σ : Γ →* GL (Fin d) ℂ := monoidHomOfForallMemZpowers hs (orderOf_dvd_of_pow_eq_one hA'l)
  have hσs : σ s = A' := monoidHomOfForallMemZpowers_apply_gen hs _
  let H : Subgroup Γ :=
    { carrier := {t | ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹}
      mul_mem' := by
        intro a b ha hb g
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, MulAut.mul_apply, ha, hb, map_mul]; group
      one_mem' := by intro g; simp
      inv_mem' := by
        intro a ha g
        simp only [Set.mem_setOf_eq] at *
        have := ha ((φ a⁻¹) g)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
        rw [map_inv σ]
        calc ρ (φ a⁻¹ g) = (σ a)⁻¹ * (σ a * ρ (φ a⁻¹ g) * (σ a)⁻¹) * σ a := by group
          _ = (σ a)⁻¹ * ρ g * ((σ a)⁻¹)⁻¹ := by rw [← this]; group }
  have hsH : s ∈ H := fun g => by rw [hσs]; exact hA's g
  have hall : ∀ t, ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹ := fun t => (Subgroup.zpowers_le.mpr hsH) (hs t)
  let Λ : G ⋊[φ] Γ →* GL (Fin d) ℂ := SemidirectProduct.lift ρ σ (fun t => by
    ext g : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hall t g)
  refine ⟨fun x => Matrix.trace ((Λ x : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ), ?_, ?_⟩
  · exact (GlobalTheory.BI.matrixChar_iff_isChar _ _).mp ⟨d, Λ, fun x => rfl⟩
  · intro g
    simp only [Λ, SemidirectProduct.lift_inl]
    exact (hρ g).symm

end GlobalTheory.StableExt
