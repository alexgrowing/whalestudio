import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
  ring

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm, ← H.h_herm]

def hlin (u : V) : V →ₗ[E] E where
  toFun v := H.h v u
  map_add' a b := H.h_add_left a b u
  map_smul' a v := by rw [H.h_smul_left]; rfl

end Basic

section Proj

variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]

theorem sub_proj_mem {A B : Submodule E V} (hAB : IsCompl A B) (x : V) :
    x - (A.projectionOnto B hAB x : V) ∈ B := by
  rw [← Submodule.projectionOnto_apply_eq_zero_iff hAB, map_sub,
    Submodule.projectionOnto_apply_left, sub_self]

theorem mem_of_proj_eq_zero {A B : Submodule E V} (hAB : IsCompl A B) {x : V}
    (h : (A.projectionOnto B hAB x : V) = 0) : x ∈ B := by
  exact (Submodule.projectionOnto_apply_eq_zero_iff hAB).1 (Subtype.ext h)

end Proj

set_option linter.deprecated false in
theorem pair_of (hR : Riesz) (hS : Scale) (hO : PI.LocHerm.LocOProj) : Pair := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H abelian₂ hL A B hAB orth u hu
  have e : Submodule.linearProjOfIsCompl A B hAB = A.projectionOnto B hAB := rfl
  rw [e]
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy hyA
    have hxB := sub_proj_mem hAB x
    have h1 : H.h x y = H.h (A.projectionOnto B hAB x : V) y := by
      have e2 := H.h_add_left (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V)) y
      rw [add_sub_cancel, (orth y hyA _ hxB).2, add_zero] at e2
      exact e2
    rw [← h1]
    exact (hL.2.2 x).1 hx y hy
  · intro hyp

    let pB : V →ₗ[E] V := B.subtype ∘ₗ B.projectionOnto A hAB.symm
    have pB_apply : ∀ v, pB v = (B.projectionOnto A hAB.symm v : V) := fun v => rfl
    let P : Submodule M.L.O V := abelian₂.map (pB.restrictScalars M.L.O)
    let π : abelian₂ →ₗ[M.L.O] P := (pB.restrictScalars M.L.O).submoduleMap abelian₂
    have hπ : Function.Surjective π := LinearMap.submoduleMap_surjective _ _
    have hπv : ∀ l : abelian₂, (π l : V) = pB l := fun l => rfl
    have hPfg : P.FG := hL.1.map _
    have : Module.Projective M.L.O P := hO F E M hM V P hPfg
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    have hsp : ∀ p : P, pB (s p : V) = p := by
      intro p
      have := congrArg Subtype.val (LinearMap.congr_fun hs p)
      rw [← hπv]
      exact this
    let Q : Submodule M.L.O V := LinearMap.range (abelian₂.subtype ∘ₗ s)
    let W : Submodule E V := Submodule.span E (Q : Set V)
    have hsW : ∀ p : P, (s p : V) ∈ W := fun p => Submodule.subset_span ⟨p, rfl⟩

    let d : abelian₂ → V := fun l => (l : V) - s (π l)
    have hdA : ∀ l : abelian₂, d l ∈ A := by
      intro l
      apply mem_of_proj_eq_zero hAB.symm
      rw [← pB_apply, map_sub, hsp, hπv, sub_self]
    have hdL : ∀ l : abelian₂, d l ∈ abelian₂ := fun l => abelian₂.sub_mem l.2 (s (π l)).2
    have hcompl : IsCompl A W := by
      refine isCompl_iff.2 ⟨?_, codisjoint_iff.2 ?_⟩
      · rw [Submodule.disjoint_def]
        intro w hwA hwW
        obtain ⟨r, hr0, hrw⟩ := hS M hM V Q w hwW
        obtain ⟨p, hp⟩ := hrw
        have hp' : (s p : V) = algebraMap F E r • w := hp
        have hpA : algebraMap F E r • w ∈ A := A.smul_mem _ hwA
        have h0 : (p : V) = 0 := by
          rw [← hsp p, hp', pB_apply]
          rw [Submodule.projectionOnto_apply_eq_zero_iff hAB.symm |>.2 hpA]
          rfl
        have hp0 : p = 0 := Subtype.ext h0
        have hrw0 : algebraMap F E r • w = 0 := by rw [← hp', hp0, map_zero]; rfl
        have : (algebraMap F E (r : F)⁻¹) • (algebraMap F E r • w) = w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hr0, map_one, one_smul]
        rw [← this, hrw0, smul_zero]
      · rw [eq_top_iff, ← hL.2.1, Submodule.span_le]
        intro l hl
        have : l = d ⟨l, hl⟩ + (s (π ⟨l, hl⟩) : V) := by simp [d]
        rw [this]
        exact Submodule.add_mem_sup (hdA _) (hsW _)
    let pA' := A.projectionOnto W hcompl
    have hpA'd : ∀ l : abelian₂, (pA' l : V) = d l := by
      intro l
      have : (l : V) = d l + (s (π l) : V) := by simp [d]
      rw [this, map_add, Submodule.projectionOnto_apply_of_mem_right hcompl (hsW _), add_zero,
        Submodule.projectionOnto_apply_of_mem_left hcompl (hdA l)]
    let f : V →ₗ[E] E := hlin H u ∘ₗ A.subtype ∘ₗ pA'
    have hfA : ∀ y ∈ A, f y = H.h y u := by
      intro y hy
      show H.h (pA' y : V) u = H.h y u
      rw [Submodule.projectionOnto_apply_of_mem_left hcompl hy]
    have hfL : ∀ l : abelian₂, f l = H.h (d l) u := by
      intro l
      show H.h (pA' l : V) u = H.h (d l) u
      rw [hpA'd]
    obtain ⟨x, hx⟩ := hR M V H f
    have hxL : x ∈ abelian₂ := by
      refine (hL.2.2 x).2 (fun y hy => ?_)
      rw [H.h_herm y x, hx y, hfL ⟨y, hy⟩, H.h_herm u (d ⟨y, hy⟩)]
      exact PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _
        (PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _ (hyp _ (hdL _) (hdA _)))
    refine ⟨x, hxL, ?_⟩
    set z : V := (A.projectionOnto B hAB x : V) - u with hz
    have hzA : z ∈ A := A.sub_mem (A.projectionOnto B hAB x).2 hu
    have key : ∀ a ∈ A, H.h a z = 0 := by
      intro a ha
      have hxB := sub_proj_mem hAB x
      have e1 : H.h a x = H.h a (A.projectionOnto B hAB x : V) := by
        have e2 := h_add_right H a (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V))
        rw [add_sub_cancel, (orth a ha _ hxB).1, add_zero] at e2
        exact e2
      rw [hz, h_sub_right, ← e1, hx a, hfA a ha, sub_self]
    have hz0 : z = 0 := by
      refine H.nondeg z (fun v => ?_)
      have hvB := sub_proj_mem hAB v
      have e3 := h_add_right H z (A.projectionOnto B hAB v : V) (v - (A.projectionOnto B hAB v : V))
      rw [add_sub_cancel, (orth z hzA _ hvB).1, add_zero] at e3
      rw [e3, H.h_herm _ z, key _ (A.projectionOnto B hAB v).2, map_zero]
    exact sub_eq_zero.1 hz0

end PI.LocHerm.Glue
