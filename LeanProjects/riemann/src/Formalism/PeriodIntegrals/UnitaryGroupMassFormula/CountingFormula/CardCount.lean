import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramCondIff

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem card_count (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (hG1 : ∀ a a', G₀ a a' ∈ M.L.O) :
    Nat.card (Set.range fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
        Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) =
    Nat.card {X : ι → Fin n → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} := by
  let Φ : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} →
      {X : ι → Fin n → k // LinearIndependent k X ∧
        ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} :=
    fun v => ⟨fun a => red hR (v.1 a), (prim_iff hR H hϖ o2 o3 v.1 v.2.1.1).1 v.2.1,
      fun a a' => (gram_cond_iff hR H hint q rfrob (v.2.1.1 a') (v.2.1.1 a) (G₀ a a') (hG1 a a')).1 (v.2.2 a a')⟩
  have hsurj : Function.Surjective Φ := by
    intro X
    choose x hxΛ hxr using fun a => red_lift hR (X.1 a)
    have hfx : (fun a => red hR (x a)) = X.1 := funext hxr
    have hli : LinearIndependent k (fun a => red hR (x a)) := by rw [hfx]; exact X.2.1
    refine ⟨⟨x, (prim_iff hR H hϖ o2 o3 x hxΛ).2 hli, fun a a' =>
      (gram_cond_iff hR H hint q rfrob (hxΛ a') (hxΛ a) (G₀ a a') (hG1 a a')).2 ?_⟩, ?_⟩
    · rw [hxr, hxr]; exact X.2.2 a a'
    · exact Subtype.ext hfx
  refine Nat.card_congr ((Setoid.quotientKerEquivRange _).symm.trans
    ((Quotient.congrRight ?_).trans (Setoid.quotientKerEquivOfSurjective Φ hsurj)))
  intro v v'
  rw [Setoid.ker_def, Setoid.ker_def]
  constructor
  · intro h
    apply Subtype.ext
    funext a
    have h1 := congrFun h a
    rw [Submodule.Quotient.eq] at h1
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).1 h1
  · intro h
    funext a
    have h1 := congrFun (congrArg Subtype.val h) a
    rw [Submodule.Quotient.eq]
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).2 h1

end FC

end PI.UnitaryGroupMassFormula.CntFormula
