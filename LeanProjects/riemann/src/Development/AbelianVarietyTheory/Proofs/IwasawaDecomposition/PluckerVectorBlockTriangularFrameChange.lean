import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_update_eq_zero_of_mem_span_others {S N : Type} [CommRing S]
    [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S) (v : Fin k → N) (i : Fin k)
    {x : N} (hx : x ∈ Submodule.span S (v '' {j | j ≠ i})) :
    F (Function.update v i x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≠ i := hj
    exact F.map_eq_zero_of_eq (Function.update v i (v j)) (i := i) (j := j)
      (by simp [Function.update_of_ne hj']) (Ne.symm hj')
  | zero => exact F.map_update_zero v i
  | add y z _ _ hy hz => rw [F.map_update_add, hy, hz, add_zero]
  | smul a y _ hy => rw [F.map_update_smul, hy, smul_zero]

open AlgebraicGeometry CategoryTheory Limits NumberField in
private theorem wedgeForm_eq_prod_mul_of_triangular_change {T : Type} {m : T → ℕ} {S N : Type}
    [CommRing S] [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S)
    (c c' : _root_.GlobalTheory.FlagEmb.Let m → N) (d : _root_.GlobalTheory.FlagEmb.Let m → S)
    (ht : ∀ z : _root_.GlobalTheory.FlagEmb.Let m, c' z - d z • c z ∈
      Submodule.span S ((fun j => c ⟨z.fst, j⟩) '' {j | j < z.snd}))
    (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    F (fun l => c' (e l)) = (∏ l, d (e l)) * F (fun l => c (e l)) := by
  classical
  obtain ⟨_, hdown⟩ := he
  let w : Finset (Fin k) → Fin k → N := fun s l => if l ∈ s then c' (e l) else c (e l)
  have key : ∀ s : Finset (Fin k), F (w s) = (∏ l ∈ s, d (e l)) * F (w ∅) := by
    intro s
    refine Finset.induction_on_min_value (fun l => ((e l).snd : ℕ)) s ?_ ?_
    · simp
    · intro a s ha hmin ih
      have hw : w (insert a s) = Function.update (w s) a
          (d (e a) • w s a + (c' (e a) - d (e a) • c (e a))) := by
        funext l
        by_cases hl : l = a
        · subst hl
          simp [w, ha]
        · simp [w, hl, Function.update_of_ne hl]
      have hzero : F (Function.update (w s) a (c' (e a) - d (e a) • c (e a))) = 0 := by
        refine wedgeForm_update_eq_zero_of_mem_span_others F (w s) a ?_
        refine Submodule.span_mono ?_ (ht (e a))
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (j : ℕ) < ((e a).snd : ℕ) := hj
        obtain ⟨l', hl'⟩ := hdown a j hj
        have hsnd : ((e l').snd : ℕ) = j := by
          have := congrArg (fun z : _root_.GlobalTheory.FlagEmb.Let m => (z.snd : ℕ)) hl'
          simpa using this
        have hne : l' ≠ a := by
          rintro rfl
          omega
        have hns : l' ∉ s := by
          intro h
          have := hmin l' h
          omega
        refine ⟨l', hne, ?_⟩
        simp [w, hns, hl']
      rw [hw, F.map_update_add, F.map_update_smul, Function.update_eq_self, hzero,
        Finset.prod_insert ha, ih, smul_eq_mul, add_zero, mul_assoc]
  have h1 : w Finset.univ = fun l => c' (e l) := by
    funext l
    simp [w]
  have h2 : w ∅ = fun l => c (e l) := by
    funext l
    simp [w]
  have := key Finset.univ
  rwa [h1, h2] at this

open AlgebraicGeometry CategoryTheory Limits NumberField in

theorem _root_.GlobalTheory.FlagEmb.plk_tri (T : Type) (m : T → ℕ) (S : Type) [CommRing S]
    (M : ℕ) (c c' : _root_.GlobalTheory.FlagEmb.Let m → Fin (M + 1) → S)
    (d : _root_.GlobalTheory.FlagEmb.Let m → S) (k : ℕ) (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m)
    (ht : _root_.GlobalTheory.FlagEmb.Tri c c' d) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    _root_.GlobalTheory.FlagEmb.plk c' e = (∏ l, d (e l)) • _root_.GlobalTheory.FlagEmb.plk c e := by
  funext q
  have := wedgeForm_eq_prod_mul_of_triangular_change
    ((Matrix.detRowAlternating (n := Fin k) (R := S)).compLinearMap
      (LinearMap.funLeft S S (_root_.GlobalTheory.FlagEmb.plE M k q))) c c' d ht e he
  unfold _root_.GlobalTheory.FlagEmb.plk
  simp only [Pi.smul_apply, smul_eq_mul]
  exact this

end GlobalTheory.FlagEmb
