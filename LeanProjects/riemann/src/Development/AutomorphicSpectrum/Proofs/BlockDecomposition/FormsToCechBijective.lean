import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem res_bijective_of_le {T : TopCat.{0}} (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) {V W : Opens T}
    (h : V ≤ W) (h' : W ≤ V) : Function.Bijective (res P h) :=
  Function.bijective_iff_has_inverse.2
    ⟨res P h', fun x => by rw [res_res, res_refl], fun x => by rw [res_res, res_refl]⟩

theorem formCoch_bijective {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {ι : Type} (U : ι → X.Opens)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a n : ℕ) :
    Function.Bijective (formCoch q U a n) := by
  have hb : ∀ i : Fin (n + 1) → ι, Function.Bijective
      (fun x => res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)
        (toOm q a (Pb.capO U i) x)) := fun i =>
    (res_bijective_of_le _ (inter_le_capO U i) (le_of_eq (inter_eq_iInf U i).symm)).comp
      (GlobalTheory.HodgeCoh.toOm_bijective q a (hUaff n i))
  refine ⟨fun c c' h => funext fun i => (hb i).1 (congrFun h i), fun σ => ?_⟩
  choose c hc using fun i => (hb i).2 (σ i)
  exact ⟨c, funext hc⟩

theorem formToCO_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  intro K _ X q ι U hUaff a j
  have hB := formCoch_bijective q U hUaff a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
    have hx' : formToCO q U a j ((Glob.formCos q U a).cx.cls c hc') = 0 := hx
    rw [formToCO_cls, GroundTheory.Arith.SchemeCoh.cls_eq_zero_iff] at hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change c ∈ (Glob.formCos q U a).cx.B j
    cases j with
    | zero =>
      rw [coboundaries_zero, AddSubgroup.mem_bot] at hx'
      exact (hB 0).1 (hx'.trans (map_zero _).symm)
    | succ n =>
      rw [coboundaries_succ] at hx'
      obtain ⟨τ, hτ⟩ := hx'
      obtain ⟨b, rfl⟩ := (hB n).2 τ
      exact ⟨b, (hB (n + 1)).1 ((formCoch_d q U a n b).trans hτ)⟩
  · intro y
    obtain ⟨σ, hσ, rfl⟩ := exists_cls (P := (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj) (U := U) (n := j) y
    obtain ⟨c, rfl⟩ := (hB j).2 σ
    have hc : (Glob.formCos q U a).cx.d j c = 0 :=
      (hB (j + 1)).1 (((formCoch_d q U a j c).trans hσ).trans (map_zero _).symm)
    exact ⟨(Glob.formCos q U a).cx.cls c hc, formToCO_cls q U a c hc⟩

end GlobalTheory.CompanionTheory.OmCech
