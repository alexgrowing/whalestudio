import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w

namespace GlobalTheory.CompanionTheory.OneResProof

variable {R : Type} [CommRing R]

section Abstract

variable (D : DCx.{w} R)

def IsB (p : ℕ) : ∀ q, D.X p q → Prop
  | 0, y => y = 0
  | q + 1, y => ∃ u, D.dv p q u = y

def EZ (q : ℕ) : Prop := ∀ p (y : D.X (p + 1) q), D.dv (p + 1) q y = 0 → D.dh (p + 1) q y = 0 →
  ∃ x, D.dv p q x = 0 ∧ D.dh p q x = y

variable {D}

theorem eb (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u)
    {q : ℕ} (hZ : EZ D q) (p : ℕ) (u : D.X (p + 1) q) (hy : D.dh (p + 1) (q + 1) (D.dv (p + 1) q u) = 0) :
    ∃ t, D.dh p (q + 1) (D.dv p q t) = D.dv (p + 1) q u := by
  have h1 : D.dv (p + 2) q (D.dh (p + 1) q u) = 0 := by rw [← D.hv, hy]
  obtain ⟨w, hw, hw'⟩ := hZ (p + 1) (D.dh (p + 1) q u) h1 (D.hh _ _ _)
  obtain ⟨t, ht⟩ := hrow q p (u - w) (by rw [map_sub, hw', sub_self])
  exact ⟨t, by rw [D.hv, ht, map_sub, hw, sub_zero]⟩

theorem ez (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u) (a : ℕ)
    (hcol : ∀ p q, q ≠ a → ∀ y : D.X p q, D.dv p q y = 0 → IsB D p q y)
    (hA : ∀ p (y : D.X (p + 1) a), D.dv (p + 1) a y = 0 → D.dh (p + 1) a y = 0 →
      ∃ x, D.dv p a x = 0 ∧ IsB D (p + 1) a (y - D.dh p a x)) (q : ℕ) : EZ D q := by
  induction q with
  | zero =>
    intro p y hv hh
    by_cases h : 0 = a
    · subst h
      obtain ⟨x, hx, hb⟩ := hA p y hv hh
      exact ⟨x, hx, (sub_eq_zero.1 hb).symm⟩
    · exact ⟨0, map_zero _, by rw [map_zero]; exact (hcol _ 0 h y hv : y = 0).symm⟩
  | succ q ih =>
    intro p y hv hh
    by_cases h : q + 1 = a
    · subst h
      obtain ⟨x, hx, u, hu⟩ := hA p y hv hh
      obtain ⟨t, ht⟩ := eb hrow ih p u (by rw [hu, map_sub, hh, D.hh, sub_zero])
      exact ⟨x + D.dv p q t, by rw [map_add, hx, D.vv, add_zero], by rw [map_add, ht, hu]; abel⟩
    · obtain ⟨u, rfl⟩ : ∃ u, D.dv (p + 1) q u = y := hcol _ _ h y hv
      obtain ⟨t, ht⟩ := eb hrow ih p u hh
      exact ⟨D.dv p q t, D.vv _ _ _, ht⟩

end Abstract

variable {ι : Type} [DecidableEq ι]

theorem cech_nat {P Q : PM.{w} R ι} (φ : ∀ S, P.M S →ₗ[R] Q.M S)
    (nat : ∀ {S T : Finset ι} (h : S ⊆ T) x, φ T (P.res h x) = Q.res h (φ S x)) (p : ℕ) (x : P.cech.X p)
    (t : Fin (p + 2) → ι) : φ _ (P.cech.d p x t) = Q.cech.d p (fun i => φ _ (x i)) t := by
  rw [Cos.d_apply, Cos.d_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact nat _ _

abbrev dcx (A : Sy.{w} R ι) : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := funext fun i => (A.K (ent i)).dd q (x i)
  hv p q x := funext fun t => (cech_nat (P := A.term q) (Q := A.term (q + 1)) (fun S => (A.K S).d q)
    (fun h x => (A.res h).comm _ x) p x t).symm

abbrev zpm (A : Sy.{w} R ι) (a : ℕ) : PM.{w} R ι where
  M S := (A.K S).Z a
  res h := (A.res h).mapZ a
  res_id S h x := Subtype.ext (A.res_id S h a x.1)
  res_comp h h' x := Subtype.ext (A.res_comp h h' a x.1)

theorem isB_of (A : Sy.{w} R ι) (p q : ℕ) (y : (dcx A).X p q) (h : ∀ i, y i ∈ (A.K (ent i)).B q) : IsB (dcx A) p q y := by
  cases q with
  | zero => exact funext fun i => h i
  | succ q =>
    choose u hu using h
    exact ⟨u, funext hu⟩

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem hcol (A : Sy.{w} R ι) (a : ℕ) (hO : A.One a) (p q : ℕ) (hq : q ≠ a) (y : (dcx A).X p q)
    (hy : (dcx A).dv p q y = 0) : IsB (dcx A) p q y := by
  refine isB_of A p q y fun i => ?_
  have hs := hO (ent i) (ent_nonempty i) q hq
  have hi : (A.K (ent i)).d q (y i) = 0 := congrFun hy i
  have h0 : (Submodule.Quotient.mk ⟨y i, hi⟩ : (A.K (ent i)).H q) = 0 := Subsingleton.elim _ _
  have h2 : (⟨y i, hi⟩ : (A.K (ent i)).Z q) ∈ ((A.K (ent i)).B q).submoduleOf ((A.K (ent i)).Z q) :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h2

theorem hrow (A : Sy.{w} R ι) (hD : A.Desc) (q p : ℕ) (u : (dcx A).X (p + 1) q) (hu : (dcx A).dh (p + 1) q u = 0) :
    ∃ t, (dcx A).dh p q t = u := by
  obtain ⟨t, ht⟩ := (hD q).2.2.2 p u hu
  exact ⟨t, ht.trans (one_smul _ _)⟩

theorem hA (A : Sy.{w} R ι) (a : ℕ)
    (hres : (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype) (p : ℕ) (y : (dcx A).X (p + 1) a)
    (hv : (dcx A).dv (p + 1) a y = 0) (hh : (dcx A).dh (p + 1) a y = 0) :
    ∃ x, (dcx A).dv p a x = 0 ∧ IsB (dcx A) (p + 1) a (y - (dcx A).dh p a x) := by
  have natI : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      ((zpm A a).cech.d p z t).1 = (dcx A).dh p a (fun i => (z i).1) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.term a) (fun S => ((A.K S).Z a).subtype) (fun h x => rfl) p z t
  have natQ : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      Submodule.Quotient.mk ((zpm A a).cech.d p z t) =
        (A.coh a).cech.d p (fun i => Submodule.Quotient.mk (z i)) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.coh a) (fun S => Submodule.mkQ _) (fun h x => rfl) p z t
  let y' : (zpm A a).cech.X (p + 1) := fun i => ⟨y i, congrFun hv i⟩
  have h0 : (zpm A a).cech.d (p + 1) y' = 0 := funext fun t => Subtype.ext ((natI (p + 1) y' t).trans (congrFun hh t))
  obtain ⟨c, hc⟩ := hres.2.2.2 p (fun i => Submodule.Quotient.mk (y' i)) (funext fun t => by
    have := natQ (p + 1) y' t
    rw [h0] at this
    exact this.symm)
  have hlift : ∀ i, ∃ z : (A.K (ent i)).Z a, Submodule.Quotient.mk z = c i := fun i =>
    Submodule.Quotient.mk_surjective _ (c i)
  choose z hz using hlift
  refine ⟨fun i => (z i).1, funext fun i => (z i).2, isB_of A _ _ _ fun t => ?_⟩
  have h1 : (Submodule.Quotient.mk (y' t - (zpm A a).cech.d p z t) : (A.K (ent t)).H a) = 0 := by
    rw [Submodule.Quotient.mk_sub, natQ, sub_eq_zero]
    have e : (fun i => Submodule.Quotient.mk (z i)) = c := funext hz
    rw [e]
    exact (congrFun (hc.trans (one_smul R _)) t).symm
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
  have e : (y - (dcx A).dh p a fun i => (z i).1) t = (y' t - (zpm A a).cech.d p z t).1 := by
    rw [Submodule.coe_sub, natI]
    rfl
  rw [e]
  exact h2

theorem high (A : Sy.{w} R ι) (a : ℕ) (hD : A.Desc) (hO : A.One a) (hZ : ∀ q, EZ (dcx A) q) (q : ℕ) (hq : q + 1 ≠ a) :
    Subsingleton ((A.K ∅).H (q + 1)) := by
  have hall : ∀ h : (A.K ∅).H (q + 1), h = 0 := by
    intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [Submodule.Quotient.mk_eq_zero]
    change x ∈ (A.K ∅).B (q + 1)
    have hx' : (A.K ∅).d (q + 1) x = 0 := hx
    have hev : (dcx A).dv 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := funext fun i => by
      change (A.K (ent i)).d (q + 1) ((A.res _).f (q + 1) x) = 0
      rw [(A.res _).comm, hx', map_zero]
    obtain ⟨u, hu⟩ : ∃ u, (dcx A).dv 0 q u = (A.term (q + 1)).aug x := hcol A a hO 0 (q + 1) hq _ hev
    have hdh : (dcx A).dh 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := (hD (q + 1)).1 x
    obtain ⟨v, hv, hv'⟩ := hZ q 0 ((dcx A).dh 0 q u) (by rw [← (dcx A).hv, hu, hdh]) ((dcx A).hh _ _ _)
    obtain ⟨s, hs⟩ := (hD q).2.2.1 (u - v) (by
      have : (dcx A).dh 0 q (u - v) = 0 := by rw [map_sub, hv', sub_self]
      exact this)
    rw [one_smul] at hs
    have h1 : (A.term (q + 1)).aug ((A.K ∅).d q s) = (A.term (q + 1)).aug x := by
      have e : (dcx A).dv 0 q ((A.term q).aug s) = (A.term (q + 1)).aug ((A.K ∅).d q s) :=
        funext fun i => (A.res _).comm q s
      rw [← e, hs, map_sub, hv, sub_zero, hu]
    have h2 := (hD (q + 1)).2.1 ((A.K ∅).d q s - x) (by rw [map_sub, h1, sub_self])
    rw [one_smul, sub_eq_zero] at h2
    exact ⟨s, h2⟩
  exact ⟨fun h₁ h₂ => by rw [hall h₁, hall h₂]⟩

theorem oneRes_of_oneLow : OneLow → OneRes := by
  intro hL R _ ι _ A a hD hO hres
  obtain ⟨hlow, hinj, hex⟩ := hL R ι A a hD hO
  have hZ : ∀ q, EZ (dcx A) q := ez (hrow A hD) a (hcol A a hO) (hA A a hres)
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hj with h | h
    · exact hlow j h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact high A a hD hO hZ q hj
  · unfold PM.Ex Cx.ResUpTo
    refine ⟨fun x => (hex _).2 ⟨x, rfl⟩, fun x hx => ?_, fun y hy => ?_, hres.2.2.2⟩
    · rw [one_smul]
      exact hinj (hx.trans (map_zero _).symm)
    · obtain ⟨x, rfl⟩ := (hex y).1 hy
      exact ⟨x, (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.OneResProof

end
