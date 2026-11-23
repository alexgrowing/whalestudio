import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.WeilOneD

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC UpperTheory.Et
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem UpperTheory.power_zero_isIso {S : Scheme.{0}} (A : Over S) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let g : Over.mk (𝟙 S) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let f : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 S) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have hfg : f ≫ g = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨g.left, ?_, ?_⟩⟩
  · have h := congrArg (fun x => x.left) hfg
    simpa [f] using h
  · simpa using Over.w g

private theorem UpperTheory.power_succ_lift {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (a : T ⟶ GlobalTheory.KS.pow A m) (b : T ⟶ A) :
    ∃ l : T ⟶ GlobalTheory.KS.pow A (m + 1),
      l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) = a ∧
      l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) = b := by
  refine ⟨Pi.lift fun j => Fin.lastCases (motive := fun _ => T ⟶ A) b
    (fun i => a ≫ Pi.π (fun _ : Fin m => A) i) j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    simp
  · simp

private theorem UpperTheory.power_succ_lift_unique {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (l l' : T ⟶ GlobalTheory.KS.pow A (m + 1))
    (h₁ : l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) =
      l' ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc))
    (h₂ : l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) =
      l' ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)) : l = l' := by
  refine Pi.hom_ext _ _ fun j => ?_
  induction j using Fin.lastCases with
  | last => exact h₂
  | cast i => simpa using congrArg (· ≫ Pi.π (fun _ : Fin m => A) i) h₁

theorem UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback :
    ∀ {S : Scheme.{0}} (A : Over S), IsIso (GlobalTheory.KS.pow A 0).hom ∧ ∀ m : ℕ, ∃ (u : (GlobalTheory.KS.pow A (m + 1)).left ⟶ (GlobalTheory.KS.pow A m).left) (v : (GlobalTheory.KS.pow A (m + 1)).left ⟶ A.left), IsPullback u v (GlobalTheory.KS.pow A m).hom A.hom ∧ u ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A (m + 1)).hom := by
  intro S A
  refine ⟨UpperTheory.power_zero_isIso A, fun m => ?_⟩
  let P : GlobalTheory.KS.pow A (m + 1) ⟶ GlobalTheory.KS.pow A m :=
    Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc
  let Q : GlobalTheory.KS.pow A (m + 1) ⟶ A := Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)
  have w : P.left ≫ (GlobalTheory.KS.pow A m).hom = Q.left ≫ A.hom := (Over.w P).trans (Over.w Q).symm
  have hL := fun s : PullbackCone (GlobalTheory.KS.pow A m).hom A.hom =>
    UpperTheory.power_succ_lift A m (Over.mk (s.snd ≫ A.hom)) (Over.homMk s.fst s.condition)
      (Over.homMk s.snd rfl)
  refine ⟨P.left, Q.left, IsPullback.of_isLimit' ⟨w⟩
    (PullbackCone.IsLimit.mk w (fun s => (hL s).choose.left) ?_ ?_ ?_), Over.w P⟩
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.1]
    rfl
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.2]
    rfl
  · intro s n hn1 hn2
    have hn : n ≫ (GlobalTheory.KS.pow A (m + 1)).hom = s.snd ≫ A.hom := by
      rw [← Over.w Q, ← Category.assoc, hn2]
    let N : Over.mk (s.snd ≫ A.hom) ⟶ GlobalTheory.KS.pow A (m + 1) := Over.homMk n hn
    have h1 : N ≫ P = (hL s).choose ≫ P := by
      rw [(hL s).choose_spec.1]
      apply (Over.forget S).map_injective
      simpa [N] using hn1
    have h2 : N ≫ Q = (hL s).choose ≫ Q := by
      rw [(hL s).choose_spec.2]
      apply (Over.forget S).map_injective
      simpa [N] using hn2
    exact congrArg (fun x => x.left) (UpperTheory.power_succ_lift_unique A m _ N _ h1 h2)
