import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace RootOfUnityLemmas

theorem pick_neg {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  rw [dif_neg h]

theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : x.cast hn hi = 0) : x = 0 := by
  subst hn; subst hi; exact h

theorem res_id {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (a : Sec F X) : Sec.res (𝟙 X) a = a := by
  simp [Sec.res]

theorem resGen_closed (hF : FormalIn) (q : ℕ) (s : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    Sec.map ((res _ (tw q s)).d 0 1) (resGen s ζ) = 0 := by
  obtain ⟨-, e, -, he⟩ := hF.a9 (ZMod q) (tw q s)
  obtain ⟨α, -, hα⟩ := he X (twGen s ζ)
  have h := ((hF.et.sch (ZMod q) X (res _ (tw q s)) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
  rw [hα] at h
  exact h

theorem ev_vanish {R : Type} [CommRing R] {X : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0) :
    ∀ (p : ℕ), p ≠ 0 → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U), ev α p s h U x = 0 := by
  intro p hp
  obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact fun s h' U x => h p' s h' U x

theorem isAW_conc {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}}
    (α : Cochain ((chains R).obj (sch.obj X)) I 0) (β : Cochain ((chains R).obj (sch.obj X)) J 0)
    (γ : Cochain ((chains R).obj (sch.obj X)) K (0 + 0)) (a : Sec (I.X 0) X) (b : Sec (J.X 0) X) (c : Sec (K.X 0) X)
    (hc : μ.mul X 0 0 0 (add_zero 0) a b = c)
    (hα0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 0 (by simp) U x = Sec.res x a)
    (hα1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0)
    (hβ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev β 0 0 (by simp) U x = Sec.res x b)
    (hβ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev β (p + 1) s h U x = 0)
    (hγ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 0 (0 + 0) (by simp) U x = Sec.res x c)
    (hγ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + (0 + 0) = s) (U : Scheme.{0}) (x : U ⟶ X), ev γ (p + 1) s h U x = 0) :
    μ.IsAW rfl α β γ := by
  intro N w h U x
  cases N with
  | zero =>
    subst h
    rw [Fin.sum_univ_one]
    have e1 : ev γ 0 (-((0 : ℕ) : ℤ) + (0 + 0)) rfl U x = μ.mul U 0 0 0 (add_zero 0) (ev α 0 0 (by simp) U x)
        (ev β 0 0 (by simp) U x) := by
      rw [hα0, hβ0, ← μ.nat, hc]
      exact hγ0 U x
    rw [e1]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rfl
  | succ N =>
    rw [hγ1 N w h U x]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hp : (p : ℕ) = 0
    · rw [ev_vanish β hβ1 (N + 1 - p) (by omega)]
      simp
    · rw [ev_vanish α hα1 p hp]
      simp

theorem conc_eq_one (hF : FormalIn) (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (t : ℤ) (ht : (0 : ℤ) = t)
    (c : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q t)) (0 + 0))
    (hc : ev c.1 0 (0 + 0) (by simp) X (𝟙 X) = resGen t ζ) (hn : (0 : ℤ) = 0 + 0) :
    CohomologyClass.mk c = (one q (sch.obj X)).cast hn ht := by
  subst ht
  by_cases hw : ∃ c' : Ht q (sch.obj X) 0 0, ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c' ∧
      ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ'
  · obtain ⟨α, hα, hα'⟩ : ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 0)) 0,
        CohomologyClass.mk α = one q (sch.obj X) ∧
        ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ' :=
      pick_spec hw
    rw [← hα]
    change CohomologyClass.mk c = CohomologyClass.mk α
    exact WeightedPowerFormIntegrability.mk_eq_of_ev hF.et.sch c α (hc.trans (hα' X (𝟙 X) ζ).symm)
  · have h1 : one q (sch.obj X) = 0 := pick_neg hw
    have hinv : Inv q (sch.obj X) := fun U ⟨x⟩ => (Prim.map (show U ⟶ X from x).appTop.hom ζ).2.1
    have h2 := (hF.a6ring q (sch.obj X)).1 hinv (CohomologyClass.mk c)
    rw [h1, map_zero, AddMonoidHom.zero_apply] at h2
    rw [h1, cast_zero', eq_zero_of_cast _ _ _ h2.symm]

end RootOfUnityLemmas

open RootOfUnityLemmas in

theorem root : RootsOfUnityFormal := by
  intro hF q _ X ⟨ζ⟩ i
  have hS := hF.et.sch
  obtain ⟨v, hv0, hv1⟩ := (hS (ZMod q) X (res _ (tw q (-i))) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen (-i) ζ) (resGen_closed hF q (-i) ζ)
  obtain ⟨u, hu0, hu1⟩ := (hS (ZMod q) X (res _ (tw q i)) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen i ζ) (resGen_closed hF q i ζ)
  obtain ⟨c, hc0, hc1⟩ := (hS (ZMod q) X (res _ (tw q (-i + i))) (-1) (0 + 0) 1 (by norm_num) (by norm_num)).1
    (resGen (-i + i) ζ) (resGen_closed hF q (-i + i) ζ)
  refine ⟨CohomologyClass.mk u, CohomologyClass.mk v, ?_⟩
  have hcup : cup q (CohomologyClass.mk v) (CohomologyClass.mk u) = CohomologyClass.mk c :=
    Pair.cup_spec (twPair q (-i) i) (sch.obj X) rfl v u c
      (isAW_conc (twPair q (-i) i) v.1 u.1 c.1 (resGen (-i) ζ) (resGen i ζ) (resGen (-i + i) ζ)
        (hF.et.tw q (-i) i X ζ) hv0 hv1 hu0 hu1 hc0 hc1)
  rw [hcup]
  exact conc_eq_one hF q X ζ (-i + i) (by ring) c ((hc0 X (𝟙 X)).trans (res_id _)) (by ring)

end CrystallineSemistableComparison
