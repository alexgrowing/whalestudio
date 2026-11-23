import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.CechOne

variable {R : Type} [CommRing R]

theorem mem_B_of_cls {K : Cx.{w} R} {n : ℕ} {x : K.X n} (hx : K.d n x = 0) (h : K.cls x hx = 0) : x ∈ K.B n :=
  (Submodule.Quotient.mk_eq_zero ((K.B n).submoduleOf (K.Z n))).1 h

theorem d_of_mem_B (K : Cx.{w} R) (n : ℕ) (x : K.X n) (h : x ∈ K.B n) : K.d n x = 0 := by
  cases n with
  | zero =>
    have h0 : x = 0 := h
    rw [h0, map_zero]
  | succ n =>
    obtain ⟨g, rfl⟩ := h
    exact K.dd n g

section Tic

variable {K : DCx.{w} R} {E : Cx.{w'} R} (e : DCx.AugRow E K) {a : ℕ}

def LowB (q : ℕ) : Prop :=
  (∀ p (b : K.X (p + 1) q), b ∈ (K.col (p + 1)).B q → K.dh (p + 1) q b = 0 →
    ∃ b' ∈ (K.col p).B q, K.dh p q b' = b) ∧
  (∀ b : K.X 0 q, b ∈ (K.col 0).B q → K.dh 0 q b = 0 → ∃ z ∈ E.B q, e.ε q z = b)

theorem lowB (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (hr : ∀ p q x, K.dh (p + 1) q x = 0 → ∃ y, K.dh p q y = x)
    (hc : ∀ p q, q ≠ a → ∀ x, K.dv p q x = 0 → x ∈ (K.col p).B q) : ∀ q, q ≤ a → LowB e q := by
  intro q
  induction q with
  | zero =>
    intro _
    constructor
    · intro p b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    · intro b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
  | succ q ih =>
    intro hq
    obtain ⟨i1, -⟩ := ih (by omega)
    have L1 : ∀ p (x : K.X (p + 1) q), K.dv (p + 1) q x = 0 → K.dh (p + 1) q x = 0 →
        ∃ y, K.dh p q y = x ∧ K.dv p q y = 0 := by
      intro p x hv hh
      obtain ⟨b', hb', e'⟩ := i1 p x (hc _ _ (by omega) x hv) hh
      exact ⟨b', e', d_of_mem_B (K.col p) q b' hb'⟩
    constructor
    · rintro p b ⟨c, rfl⟩ hb
      change K.dh (p + 1) (q + 1) (K.dv (p + 1) q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 (p + 1) (K.dh (p + 1) q c) hb (K.hh _ _ _)
      obtain ⟨v, hv⟩ := hr p q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨K.dv p q v, ⟨v, rfl⟩, ?_⟩
      change K.dh p (q + 1) (K.dv p q v) = K.dv (p + 1) q c
      rw [K.hv, hv, map_sub, hyv, sub_zero]
    · rintro b ⟨c, rfl⟩ hb
      change K.dh 0 (q + 1) (K.dv 0 q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 0 (K.dh 0 q c) hb (K.hh _ _ _)
      obtain ⟨z, hz⟩ := hr0 q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨E.d q z, ⟨z, rfl⟩, ?_⟩
      change e.ε (q + 1) (E.d q z) = K.dv 0 q c
      rw [← e.comm, hz, map_sub, hyv, sub_zero]

theorem mem_B_of_eps (hinj : ∀ q, Function.Injective (e.ε q)) (h : ∀ q, q ≤ a → LowB e q) {q : ℕ} (hq : q ≤ a)
    (z : E.X q) (hz : e.ε q z ∈ (K.col 0).B q) : z ∈ E.B q := by
  obtain ⟨z', hz', h'⟩ := (h q hq).2 _ hz (e.hε q z)
  rwa [← hinj q h']

theorem exists_lift (hinj : ∀ q, Function.Injective (e.ε q)) (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (h : ∀ q, q ≤ a → LowB e q) (u : K.X 0 a) (hu : K.dv 0 a u = 0) (hd : K.dh 0 a u ∈ (K.col 1).B a) :
    ∃ z b, E.d a z = 0 ∧ b ∈ (K.col 0).B a ∧ e.ε a z + b = u := by
  obtain ⟨b, hb, eb⟩ := (h a le_rfl).1 0 _ hd (K.hh _ _ _)
  obtain ⟨z, hz⟩ := hr0 a (u - b) (by rw [map_sub, eb, sub_self])
  refine ⟨z, b, hinj (a + 1) ?_, hb, by rw [hz, sub_add_cancel]⟩
  rw [← e.comm, hz, map_zero, map_sub, hu, d_of_mem_B (K.col 0) a b hb, sub_zero]

end Tic

variable {ι : Type} [DecidableEq ι]

theorem cech_d_apply (P : PM.{w} R ι) (p : ℕ) (x : P.cech.X p) (t : Fin (p + 2) → ι) :
    P.cech.d p x t = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • P.res (ent_comp t k.succAbove) (x (t ∘ k.succAbove)) := by
  rw [Cos.d_apply, Finset.sum_apply]
  rfl

theorem d_aug (P : PM.{w} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  funext t
  rw [cech_d_apply, Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • P.res _ (P.res _ x) + (-1 : ℤ) ^ 1 • P.res _ (P.res _ x) = 0
  rw [P.res_comp, P.res_comp]
  simp

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  Finset.univ_nonempty.image i

variable (A : Sy.{w} R ι)

abbrev dcx : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := by
    funext i
    exact (A.K (ent i)).dd q (x i)
  hv p q x := by
    funext t
    rw [cech_d_apply]
    change _ = (A.K (ent t)).d q ((A.term q).cech.d p x t)
    rw [cech_d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ ((A.res _).comm q _).symm

def aug : DCx.AugRow (A.K ∅) (dcx A) where
  ε q := (A.term q).aug
  hε q x := d_aug (A.term q) x
  comm q x := by
    funext i
    exact (A.res _).comm q x

theorem mem_col_B {p q : ℕ} (x : (dcx A).X p q) (h : ∀ i, x i ∈ (A.K (ent i)).B q) : x ∈ ((dcx A).col p).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := funext h
    exact h0
  | succ q =>
    choose c hc using h
    exact ⟨c, funext hc⟩

theorem col_B_mem {p q : ℕ} (x : (dcx A).X p q) (h : x ∈ ((dcx A).col p).B q) (i) : x i ∈ (A.K (ent i)).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := h
    rw [h0]
    exact Submodule.zero_mem _
  | succ q =>
    obtain ⟨c, rfl⟩ := h
    exact ⟨c i, rfl⟩

theorem oneLow : OneLow := by
  intro R _ ι _ A a hD hO
  have hinj : ∀ q, Function.Injective ((aug A).ε q) := fun q =>
    (injective_iff_map_eq_zero _).2 fun x hx => by simpa using (hD q).2.1 x hx
  have hr0 : ∀ q x, (dcx A).dh 0 q x = 0 → ∃ y, (aug A).ε q y = x := fun q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.1 x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hr : ∀ p q x, (dcx A).dh (p + 1) q x = 0 → ∃ y, (dcx A).dh p q y = x := fun p q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.2 p x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hc : ∀ p q, q ≠ a → ∀ x, (dcx A).dv p q x = 0 → x ∈ ((dcx A).col p).B q := by
    intro p q hq x hx
    refine mem_col_B A x fun i => ?_
    have hi : (A.K (ent i)).d q (x i) = 0 := congrFun hx i
    have := hO (ent i) (ent_nonempty i) q hq
    exact mem_B_of_cls hi (Subsingleton.elim _ _)
  have hL := lowB (aug A) hr0 hr hc
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL hj.le z.1 (hc 0 j hj.ne _ ?_)
    rw [(aug A).comm, show (A.K ∅).d j z.1 = 0 from z.2, map_zero]
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL le_rfl z.1 (mem_col_B A _ fun i => ?_)
    have hz : (A.K (ent i)).d a ((A.res (Finset.empty_subset _)).f a z.1) = 0 := by
      rw [(A.res _).comm, show (A.K ∅).d a z.1 = 0 from z.2, map_zero]
    exact mem_B_of_cls hz (congrFun hx i)
  · intro y
    constructor
    · intro hy
      have hs : ∀ i, ∃ u : (A.K (ent i)).Z a, Submodule.Quotient.mk u = y i := fun i =>
        Submodule.Quotient.mk_surjective _ (y i)
      choose u hu using hs
      let u' : (dcx A).X 0 a := fun i => (u i).1
      have hv : (dcx A).dv 0 a u' = 0 := funext fun i => (u i).2
      have hd : (dcx A).dh 0 a u' ∈ ((dcx A).col 1).B a := by
        refine mem_col_B A _ fun t => ?_
        have h := congrFun hy t
        rw [cech_d_apply, Fin.sum_univ_two, ← hu, ← hu] at h
        have hz : (A.K (ent t)).d a ((dcx A).dh 0 a u' t) = 0 := congrFun ((dcx A).hv 0 a u' ▸ (by rw [hv, map_zero] : (dcx A).dh 0 (a + 1) ((dcx A).dv 0 a u') = 0)) t
        refine mem_B_of_cls hz ?_
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h
        have e : (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) =
            (A.res (ent_comp t (Fin.succAbove 0))).mapZ a (u (t ∘ Fin.succAbove 0)) -
              (A.res (ent_comp t (Fin.succAbove 1))).mapZ a (u (t ∘ Fin.succAbove 1)) := by
          refine Subtype.ext ?_
          change (A.term a).cech.d 0 u' t = _
          rw [cech_d_apply, Fin.sum_univ_two]
          simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
          exact (sub_eq_add_neg _ _).symm
        change Submodule.Quotient.mk (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) = 0
        rw [e, Submodule.Quotient.mk_sub, sub_eq_add_neg]
        exact h
      obtain ⟨z, b, hz, hb, e⟩ := exists_lift (aug A) hinj hr0 hL u' hv hd
      refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
      funext i
      rw [← hu]
      change Submodule.Quotient.mk ((A.res (Finset.empty_subset _)).mapZ a ⟨z, hz⟩) = Submodule.Quotient.mk (u i)
      refine (Submodule.Quotient.eq _).2 ?_
      have hbi := col_B_mem A b hb i
      have e' : (A.term a).aug z i + b i = (u i).1 := congrFun e i
      have e2 : (A.term a).aug z i - (u i).1 = -(b i) := by
        rw [← e']
        abel
      change (A.term a).aug z i - (u i).1 ∈ (A.K (ent i)).B a
      rw [e2]
      exact neg_mem hbi
    · rintro ⟨x, rfl⟩
      exact d_aug _ x

end GlobalTheory.CompanionTheory.CechOne

end
