import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechPic

variable {X Y Z : Scheme.{0}}

def tens (A B : LB X) : LB X where
  ι := A.ι × B.ι
  U := fun p => A.U p.1 ⊓ B.U p.2
  g := fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2) ≤ A.U p.1 ⊓ A.U q.1) (A.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2) ≤ B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2)

def dual (A : LB X) : LB X where
  ι := A.ι
  U := A.U
  g := fun i j => (A.g i j)⁻¹

theorem gm_tens (A B : LB X) (r : Z ⟶ X) (z : Z) (p q : A.ι × B.ι)
    (hp : r z ∈ A.U p.1 ⊓ B.U p.2) (hq : r z ∈ A.U q.1 ⊓ B.U q.2) :
    gm r z ((tens A B).U p ⊓ (tens A B).U q) ((tens A B).g p q) =
      gm r z _ (A.g p.1 q.1) * gm r z _ (B.g p.2 q.2) :=
  have hm : r z ∈ A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2) := ⟨hp, hq⟩
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _))

theorem gm_div' (A B : LB X) (r : Z ⟶ X) (z : Z) (p q : A.ι × B.ι)
    (hp : r z ∈ A.U p.1 ⊓ B.U p.2) (hq : r z ∈ A.U q.1 ⊓ B.U q.2) :
    gm r z ((LB.div A B).U p ⊓ (LB.div A B).U q) ((LB.div A B).g p q) =
      gm r z _ (A.g p.1 q.1) * (gm r z _ (B.g p.2 q.2))⁻¹ :=
  gm_div B A r z p q ⟨hp, hq⟩

theorem isLB_dual {A : LB X} (hA : A.IsLB) : (dual A).IsLB where
  cover := hA.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hA.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hA.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h

theorem tens_eq_div (A B : LB X) : tens A B = LB.div A (dual B) := by
  unfold tens LB.div dual
  simp only [map_inv, inv_inv]

theorem isLB_tens {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) : (tens A B).IsLB := by
  rw [tens_eq_div]; exact LB.isLB_div hA (isLB_dual hB)

theorem isGen_iff_germ {A : LB X} (t : LB.Gen A) : t.IsGen ↔ ∀ (y : X) i j, y ∈ A.U i → y ∈ A.U j →
    gm (𝟙 X) y (A.U i) (t.s i) = gm (𝟙 X) y (A.U i ⊓ A.U j) (A.g i j) * gm (𝟙 X) y (A.U j) (t.s j) := by
  constructor
  · intro h y i j hi hj
    have hm : (𝟙 X : X ⟶ X) y ∈ A.U i ⊓ A.U j := ⟨hi, hj⟩
    have := congrArg (gm (𝟙 X) y _) (h i j)
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at this
  · intro h i j
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact h y i j hy.1 hy.2

theorem iso_of_chart {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X)) : LBIso A B :=
  LBIso.chartPull a (chartPullId B) (PolBaseChange.lbIso_refl hB)

theorem tens_comm_iso {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) : LBIso (tens A B) (tens B A) :=
  iso_of_chart (isLB_tens hB hA)
    { idx := fun p => (p.2, p.1)
      le := fun _ _ h => ⟨h.2, h.1⟩
      g := fun y p q hp hq => (gm_tens A B (𝟙 X) y p q hp hq).trans ((mul_comm _ _).trans
        (gm_tens B A (𝟙 X) y (p.2, p.1) (q.2, q.1) ⟨hp.2, hp.1⟩ ⟨hq.2, hq.1⟩).symm) }

theorem tens_congr_left {A A' B : LB X} (hB : B.IsLB) (h : LBIso A A') : LBIso (tens A B) (tens A' B) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A'.ι × B.ι) × (A.ι × B.ι), A'.U p.1.1 ⊓ B.U p.1.2 ⊓ (A.U p.2.1 ⊓ B.U p.2.2) ≤
      A'.U p.1.1 ⊓ A.U p.2.1 := fun p y h => ⟨h.1.1, h.2.1⟩
  have l₂ : ∀ p : (A'.ι × B.ι) × (A.ι × B.ι), A'.U p.1.1 ⊓ B.U p.1.2 ⊓ (A.U p.2.1 ⊓ B.U p.2.2) ≤
      B.U p.1.2 ⊓ B.U p.2.2 := fun p y h => ⟨h.1.2, h.2.2⟩
  refine ⟨⟨fun p => res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (B.g p.1.2 p.2.2)⟩,
    (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have v : ∀ p : (A'.ι × B.ι) × (A.ι × B.ι), y ∈ A'.U p.1.1 ⊓ B.U p.1.2 ⊓ (A.U p.2.1 ⊓ B.U p.2.2) →
      gm (𝟙 X) y _ (res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (B.g p.1.2 p.2.2)) =
        gm (𝟙 X) y (A'.U p.1.1 ⊓ A.U p.2.1) (w.s (p.1.1, p.2.1)) * gm (𝟙 X) y _ (B.g p.1.2 p.2.2) := fun p hp =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _) (gm_res _ y _ hp _))
  have e := ((isGen_iff_germ w).1 hw y (p.1.1, p.2.1) (q.1.1, q.2.1) (l₁ p hp) (l₁ q hq)).trans
    (congrArg (· * _) (gm_div' A' A (𝟙 X) y (p.1.1, p.2.1) (q.1.1, q.2.1) (l₁ p hp) (l₁ q hq)))
  refine (v p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div' (tens A' B) (tens A B) (𝟙 X) y p q hp hq).trans
    (congrArg₂ (fun a b => a * b⁻¹) (gm_tens A' B (𝟙 X) y p.1 q.1 hp.1 hq.1) (gm_tens A B (𝟙 X) y p.2 q.2 hp.2 hq.2)))
    (v q hq)).symm)
  have a := gm_cocycle hB (𝟙 X) y hp.1.2 hq.1.2 hq.2.2
  have b := gm_cocycle hB (𝟙 X) y hp.1.2 hp.2.2 hq.2.2
  have c : gm (𝟙 X) y _ (B.g p.1.2 p.2.2) =
      gm (𝟙 X) y _ (B.g p.1.2 q.1.2) * gm (𝟙 X) y _ (B.g q.1.2 q.2.2) * (gm (𝟙 X) y _ (B.g p.2.2 q.2.2))⁻¹ := by
    rw [a, ← b, mul_inv_cancel_right]
  refine (congrArg₂ (· * ·) e c).trans ?_
  have key : ∀ {G : Type} [CommGroup G] (a b c d e f : G), a * b⁻¹ * c * (d * e * f⁻¹) = a * d * (b * f)⁻¹ * (c * e) := by
    intro G _ a b c d e f
    simp only [mul_inv]
    ac_rfl
  exact key _ _ _ _ _ _

theorem iso_triv_iff (N : LB X) : LBIso (LB.triv X) N ↔ ∃ t : LB.Gen N, t.IsGen := by
  constructor
  · rintro ⟨t, ht⟩
    refine gen_chartPull (A' := N) (A := LB.div N (LB.triv X)) (h := 𝟙 X) ⟨fun i => (i, PUnit.unit), fun _ _ h => ⟨h, trivial⟩, ?_⟩ t ht
    intro y i j hi hj
    refine Eq.symm ((gm_div' N (LB.triv X) (𝟙 X) y (i, PUnit.unit) (j, PUnit.unit) ⟨hi, trivial⟩ ⟨hj, trivial⟩).trans ?_)
    simp
  · rintro ⟨t, ht⟩
    refine gen_chartPull (A' := LB.div N (LB.triv X)) (h := 𝟙 X) ⟨fun i => i.1, fun _ _ h => h.1, ?_⟩ t ht
    intro y i j hi hj
    refine (gm_div' N (LB.triv X) (𝟙 X) y i j hi hj).trans ?_
    simp

instance setoid (X : Scheme.{0}) : Setoid {L : LB X // L.IsLB} where
  r A B := LBIso A.1 B.1
  iseqv := ⟨fun A => PolBaseChange.lbIso_refl A.2, LBIso.symm, fun {A B C} => LBIso.trans A.2 B.2 C.2⟩

def Pic (X : Scheme.{0}) : Type 1 := Quotient (setoid X)

def cls (L : LB X) (hL : L.IsLB) : Pic X := Quotient.mk _ ⟨L, hL⟩

theorem cls_eq_iff {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) : cls A hA = cls B hB ↔ LBIso A B :=
  Quotient.eq (r := setoid X)

theorem cls_surj (c : Pic X) : ∃ L hL, cls L hL = c := by
  obtain ⟨⟨L, hL⟩, rfl⟩ := Quotient.exists_rep c
  exact ⟨L, hL, rfl⟩

instance : Add (Pic X) := ⟨Quotient.map₂ (fun A B => ⟨tens A.1 B.1, isLB_tens A.2 B.2⟩)
  fun A A' hA B B' hB => LBIso.trans (isLB_tens A.2 B.2) (isLB_tens A'.2 B.2) (isLB_tens A'.2 B'.2)
    (tens_congr_left B.2 hA) (LBIso.trans (isLB_tens A'.2 B.2) (isLB_tens B.2 A'.2) (isLB_tens A'.2 B'.2)
      (tens_comm_iso A'.2 B.2) (LBIso.trans (isLB_tens B.2 A'.2) (isLB_tens B'.2 A'.2) (isLB_tens A'.2 B'.2)
        (tens_congr_left A'.2 hB) (tens_comm_iso B'.2 A'.2)))⟩

instance : Zero (Pic X) := ⟨cls _ (LB.isLB_triv X)⟩

instance : Neg (Pic X) := ⟨fun c => cls _ (isLB_dual (Quotient.out c).2)⟩

theorem cls_tens {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : (tens A B).IsLB) :
    cls (tens A B) h = cls A hA + cls B hB := rfl

theorem cls_eq_zero_iff {N : LB X} (hN : N.IsLB) : cls N hN = 0 ↔ ∃ t : LB.Gen N, t.IsGen :=
  (eq_comm.trans (cls_eq_iff (LB.isLB_triv X) hN)).trans (iso_triv_iff N)

theorem cls_dual_add {A : LB X} (hA : A.IsLB) : cls _ (isLB_dual hA) + cls A hA = 0 := by
  refine (cls_eq_zero_iff (isLB_tens (isLB_dual hA) hA)).2 ⟨⟨fun p => (A.g p.1 p.2)⁻¹⟩,
    (isGen_iff_germ _).2 fun y p q hp hq => ?_⟩
  have a := gm_cocycle hA (𝟙 X) y hp.1 hq.1 hq.2
  have b := gm_cocycle hA (𝟙 X) y hp.1 hp.2 hq.2
  refine (map_inv _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_tens (dual A) A (𝟙 X) y p q hp hq).trans
    (congrArg (· * _) (map_inv _ _))) (map_inv _ _)).symm)
  have c : gm (𝟙 X) y _ (A.g p.1 p.2) =
      gm (𝟙 X) y _ (A.g p.1 q.1) * gm (𝟙 X) y _ (A.g q.1 q.2) * (gm (𝟙 X) y _ (A.g p.2 q.2))⁻¹ := by
    rw [a, ← b, mul_inv_cancel_right]
  refine (congrArg (·⁻¹) c).trans ?_
  simp only [mul_inv, inv_inv]
  exact mul_right_comm _ _ _

instance : AddGroup (Pic X) := AddGroup.ofLeftAxioms
  (fun a b c => by
    obtain ⟨A, hA, rfl⟩ := cls_surj a
    obtain ⟨B, hB, rfl⟩ := cls_surj b
    obtain ⟨C, hC, rfl⟩ := cls_surj c
    refine (cls_eq_iff (isLB_tens (isLB_tens hA hB) hC) (isLB_tens hA (isLB_tens hB hC))).2
      (iso_of_chart (isLB_tens hA (isLB_tens hB hC)) ⟨fun p => (p.1.1, p.1.2, p.2), fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩, ?_⟩)
    intro y p q hp hq
    exact ((gm_tens (tens A B) C (𝟙 X) y p q hp hq).trans (congrArg (· * _) (gm_tens A B (𝟙 X) y p.1 q.1 hp.1 hq.1))).trans
      ((mul_assoc _ _ _).trans ((gm_tens A (tens B C) (𝟙 X) y (p.1.1, p.1.2, p.2) (q.1.1, q.1.2, q.2)
        ⟨hp.1.1, hp.1.2, hp.2⟩ ⟨hq.1.1, hq.1.2, hq.2⟩).trans
        (congrArg (_ * ·) (gm_tens B C (𝟙 X) y (p.1.2, p.2) (q.1.2, q.2) ⟨hp.1.2, hp.2⟩ ⟨hq.1.2, hq.2⟩))).symm))
  (fun a => by
    obtain ⟨A, hA, rfl⟩ := cls_surj a
    refine (cls_eq_iff (isLB_tens (LB.isLB_triv X) hA) hA).2
      (iso_of_chart hA ⟨fun p => p.2, fun _ _ h => h.2, ?_⟩)
    intro y p q hp hq
    refine (gm_tens (LB.triv X) A (𝟙 X) y p q hp hq).trans ?_
    simp)
  (fun a => by
    have h := cls_dual_add (Quotient.out a).2
    have e : cls _ (Quotient.out a).2 = a := Quotient.out_eq a
    rw [e] at h
    exact h)

instance : AddCommGroup (Pic X) where
  add_comm a b := by
    obtain ⟨A, hA, rfl⟩ := cls_surj a
    obtain ⟨B, hB, rfl⟩ := cls_surj b
    exact (cls_eq_iff (isLB_tens hA hB) (isLB_tens hB hA)).2 (tens_comm_iso hA hB)

theorem cls_dual {A : LB X} (hA : A.IsLB) (h : (dual A).IsLB) : cls _ h = -cls A hA :=
  eq_neg_of_add_eq_zero_left (cls_dual_add hA)

theorem cls_div {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : (LB.div A B).IsLB) :
    cls _ h = cls A hA - cls B hB := by
  rw [sub_eq_add_neg, ← cls_dual hB (isLB_dual hB), ← cls_tens hA (isLB_dual hB) (isLB_tens hA (isLB_dual hB))]
  refine (cls_eq_iff _ _).2 (iso_of_chart (isLB_tens hA (isLB_dual hB)) ⟨fun p => p, fun _ _ h => h, ?_⟩)
  intro y p q hp hq
  exact (gm_div' A B (𝟙 X) y p q hp hq).trans ((gm_tens A (dual B) (𝟙 X) y p q hp hq).trans
    (congrArg (_ * ·) (map_inv _ _))).symm

def pull (f : Y ⟶ X) : Pic X →+ Pic Y := AddMonoidHom.mk'
  (Quotient.map (fun A => ⟨A.1.pull f, pull_isLB A.2 f⟩)
    fun A B h => LBIso.chartPull (chartPullPull A.1 f f rfl) (chartPullPull B.1 f f rfl) h)
  (fun a b => by
    obtain ⟨A, hA, rfl⟩ := cls_surj a
    obtain ⟨B, hB, rfl⟩ := cls_surj b
    have h := isLB_tens (pull_isLB hA f) (pull_isLB hB f)
    refine (cls_eq_iff (pull_isLB (isLB_tens hA hB) f) h).2 (iso_of_chart h
      ⟨fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2),
        fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩, ?_⟩)
    intro y p q hp hq
    have hp' := mem_pull.1 hp
    have hq' := mem_pull.1 hq
    refine ((gm_pull_g (tens A B) f (𝟙 Y) y p q hp hq).trans (gm_tens A B (𝟙 Y ≫ f) y _ _ hp' hq')).trans (Eq.symm ?_)
    exact (gm_tens (A.pull f) (B.pull f) (𝟙 Y) y (fun _ => (p PUnit.unit).1, fun _ => (p PUnit.unit).2)
      (fun _ => (q PUnit.unit).1, fun _ => (q PUnit.unit).2) ⟨mem_pull.2 hp'.1, mem_pull.2 hp'.2⟩
      ⟨mem_pull.2 hq'.1, mem_pull.2 hq'.2⟩).trans (congrArg₂ (· * ·)
        (gm_pull_g A f (𝟙 Y) y _ _ (mem_pull.2 hp'.1) (mem_pull.2 hq'.1))
        (gm_pull_g B f (𝟙 Y) y _ _ (mem_pull.2 hp'.2) (mem_pull.2 hq'.2))))

theorem cls_pull {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : (L.pull f).IsLB) :
    cls (L.pull f) h = pull f (cls L hL) := rfl

theorem pull_id (c : Pic X) : pull (𝟙 X) c = c := by
  obtain ⟨A, hA, rfl⟩ := cls_surj c
  exact (cls_eq_iff (pull_isLB hA _) hA).2 (iso_of_chart hA (chartPullPull A _ _ rfl))

theorem pull_comp (g : Z ⟶ Y) (f : Y ⟶ X) (c : Pic X) : pull (g ≫ f) c = pull g (pull f c) := by
  obtain ⟨A, hA, rfl⟩ := cls_surj c
  exact ((cls_eq_iff (pull_isLB (pull_isLB hA _) _) (pull_isLB hA _)).2 (iso_of_chart (pull_isLB hA _)
    (chartPullLinComb A f (fun _ : PUnit => g) (fun _ => g ≫ f) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm))).symm

theorem cls_linComb_add {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε ε' : K → ℤ) :
    cls _ (LB.isLB_linComb hL φ (ε + ε')) = cls _ (LB.isLB_linComb hL φ ε) + cls _ (LB.isLB_linComb hL φ ε') := by
  have h := isLB_tens (LB.isLB_linComb hL φ ε) (LB.isLB_linComb hL φ ε')
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun j => (j, j), fun _ _ h => ⟨h, h⟩, ?_⟩)
  intro y p q hp hq
  refine (gm_linComb L φ (ε + ε') (𝟙 Y) y p q hp hq).trans (Eq.symm ((gm_tens (LB.LinComb L φ ε) (LB.LinComb L φ ε') (𝟙 Y) y
    (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y p q hp hq)
      (gm_linComb L φ ε' (𝟙 Y) y p q hp hq)).trans ?_)))
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem cls_linComb_single {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] [DecidableEq K] (φ : K → (Y ⟶ X)) (k : K) :
    cls _ (LB.isLB_linComb hL φ (Pi.single k 1)) = pull (φ k) (cls L hL) := by
  refine (cls_eq_iff _ (pull_isLB hL _)).2 (iso_of_chart (pull_isLB hL _)
    ⟨fun j _ => j k, fun _ _ h => mem_pull.2 (Set.mem_iInter.1 h k), ?_⟩)
  intro y p q hp hq
  refine (gm_linComb L φ _ (𝟙 Y) y p q hp hq).trans (Eq.symm ((gm_pull_g L (φ k) (𝟙 Y) y (fun _ => p k) (fun _ => q k)
    (mem_pull.2 (Set.mem_iInter.1 hp k)) (mem_pull.2 (Set.mem_iInter.1 hq k))).trans ?_))
  rw [Finset.prod_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zpow_zero]) (by simp),
    Pi.single_eq_same, zpow_one]

theorem cls_linComb {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : (LB.LinComb L φ ε).IsLB) : cls _ h = ∑ k, ε k • pull (φ k) (cls L hL) := by
  classical
  let F : (K → ℤ) →+ Pic Y := AddMonoidHom.mk' (fun ε => cls _ (LB.isLB_linComb hL φ ε)) (cls_linComb_add hL φ)
  have e : ε = ∑ k, ε k • (Pi.single k 1 : K → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  show F ε = _
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, ← e]
  exact congrArg _ (cls_linComb_single hL φ k)

theorem cls_lbPow {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (lbPow L n).IsLB) : cls _ h = n • cls L hL := by
  rw [cls_linComb hL, Fintype.sum_unique, pull_id, natCast_zsmul]

end GlobalTheory.CechPic
