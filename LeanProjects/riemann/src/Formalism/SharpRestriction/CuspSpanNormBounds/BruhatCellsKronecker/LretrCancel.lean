import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
import Lemmata.GeneralBFactRightAltForm.Imports

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module

section

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem lretr_den (A : Set V) (y : V) (hy : y ∈ Submodule.span E A) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Submodule.span (𝓞 E) A := by
  first | exact Bl.general_b_fact_right_alt_form.goal1 .. | (apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_alt_form.goal1 <;> assumption)

theorem lretr_cancel (d : 𝓞 E) (hd : d ≠ 0) (x y : V) (h : d • x = d • y) : x = y := by
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  rw [← algebraMap_smul E d, ← algebraMap_smul E d] at h
  exact smul_right_injective V hdE h

theorem lretr_mem (X : Submodule E V) (d : 𝓞 E) (hd : d ≠ 0) (x : V) (h : d • x ∈ X) : x ∈ X := by
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  rw [← algebraMap_smul E d] at h
  exact (Submodule.smul_mem_iff X hdE).1 h

theorem lretr_rho (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ l : Λ, ((ρ l : Λ) : V) ∈ X) ∧ ∀ l : Λ, (l : V) ∈ X → ρ l = l := by
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have hmemN : ∀ l : Λ, l ∈ N ↔ (l : V) ∈ X := fun l => Iff.rfl
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  have : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨l, rfl⟩ := N.mkQ_surjective m
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]
      exact lretr_mem X r hr _ hrm
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  refine ⟨LinearMap.id - s ∘ₗ N.mkQ, fun l => ?_, fun l hl => ?_⟩
  · rw [← hmemN, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    show N.mkQ (l - s (N.mkQ l)) = 0
    have := LinearMap.congr_fun hs (N.mkQ l)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [map_sub, this, sub_self]
  · have h0 : N.mkQ l = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]; exact hl
    simp [h0]

end

theorem l_retr : IntegralRetraction := by
  intro E _ _ _ S Λ X hΛ
  obtain ⟨ρ, hρX, hρid⟩ := lretr_rho Λ hΛ.fg X
  obtain ⟨b, hbΛ, hbs, hbi⟩ := exists_linearIndependent E (Λ : Set S.V)
  have hspan : Submodule.span E b = ⊤ := by rw [hbs]; exact hΛ.span_eq_top
  let B : Basis b E S.V := Basis.mk hbi (by rw [Subtype.range_coe]; exact hspan.ge)
  have hB : ∀ i : b, B i = (i : S.V) := fun i => by simp [B]
  let P : S.V →ₗ[E] S.V := B.constr E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V))
  have hPb : ∀ i : b, P (i : S.V) = ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V) := fun i => by
    have h := B.constr_basis E (fun i : b => ((ρ ⟨i, hbΛ i.2⟩ : Λ) : S.V)) i
    rw [hB i] at h
    exact h
  have hPsm : ∀ (d : 𝓞 E) (y : S.V), P (d • y) = d • P y := fun d y => by
    rw [← algebraMap_smul E d, map_smul, algebraMap_smul]

  have hPspan : ∀ y (hy : y ∈ Submodule.span (𝓞 E) b) (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hyΛ; exact hPb ⟨x, hx⟩
    | zero =>
      intro hyΛ
      have : (⟨0, hyΛ⟩ : Λ) = 0 := rfl
      rw [this, map_zero, map_zero]; rfl
    | add x y hx hy ihx ihy =>
      intro hyΛ
      have hxΛ : x ∈ Λ := Submodule.span_le.2 hbΛ hx
      have hyΛ' : y ∈ Λ := Submodule.span_le.2 hbΛ hy
      have : (⟨x + y, hyΛ⟩ : Λ) = ⟨x, hxΛ⟩ + ⟨y, hyΛ'⟩ := rfl
      rw [this, map_add, map_add, ihx hxΛ, ihy hyΛ']; rfl
    | smul c x hx ihx =>
      intro hyΛ
      have hxΛ : x ∈ Λ := Submodule.span_le.2 hbΛ hx
      have : (⟨c • x, hyΛ⟩ : Λ) = c • ⟨x, hxΛ⟩ := rfl
      rw [hPsm, this, map_smul, ihx hxΛ]; rfl
  have hPΛ : ∀ y (hyΛ : y ∈ Λ), P y = ((ρ ⟨y, hyΛ⟩ : Λ) : S.V) := by
    intro y hyΛ
    obtain ⟨d, hd, hdy⟩ := lretr_den (b : Set S.V) y (by rw [hspan]; trivial)
    apply lretr_cancel d hd
    rw [← hPsm, hPspan _ hdy (Λ.smul_mem d hyΛ)]
    have : (⟨d • y, Λ.smul_mem d hyΛ⟩ : Λ) = d • ⟨y, hyΛ⟩ := rfl
    rw [this, map_smul]; rfl
  have hden : ∀ y : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ := by
    intro y
    obtain ⟨d, hd, hdy⟩ := lretr_den (b : Set S.V) y (by rw [hspan]; trivial)
    exact ⟨d, hd, Submodule.span_le.2 hbΛ hdy⟩
  refine ⟨P, fun x hx => ?_, fun y => ?_, fun l hl => ?_⟩
  · obtain ⟨d, hd, hdx⟩ := hden x
    apply lretr_cancel d hd
    rw [← hPsm, hPΛ _ hdx, hρid ⟨d • x, hdx⟩ (by
      show d • x ∈ X
      rw [← algebraMap_smul E d]; exact X.smul_mem _ hx)]
  · obtain ⟨d, hd, hdy⟩ := hden y
    apply lretr_mem X d hd
    rw [← hPsm, hPΛ _ hdy]
    exact hρX _
  · rw [hPΛ l hl]
    exact (ρ ⟨l, hl⟩).2

end Formalism.MainNotions.BridgeLemma

end
