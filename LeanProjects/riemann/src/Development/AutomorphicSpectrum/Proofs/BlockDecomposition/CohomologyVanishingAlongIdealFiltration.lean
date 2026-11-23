import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerEnd

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

abbrev Q (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Type 1 := CH.Cn (CH.modF A) j

abbrev dQ (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Q A j →ₗ[R] Q A (j + 1) := CH.d (CH.modF A) j

abbrev val {j : ℕ} (x : Q A j) (s : ComposableArrows C j) : A.obj (s.obj (Fin.last j)) := x s

def Vals (a : IdF A) {j : ℕ} (x : Q A j) : Prop := ∀ s, val x s ∈ a.S (s.obj (Fin.last j))

theorem dQ_apply {j : ℕ} (x : Q A j) (s : ComposableArrows C (j + 1)) :
    val (dQ A j x) s = ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)) := rfl

theorem Vals.sub {a : IdF A} {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) : Vals a (x - y) :=
  fun s => (a.S _).sub_mem (hx s) (hy s)

theorem Vals.dQ {a : IdF A} {j : ℕ} {x : Q A j} (hx : Vals a x) : Vals a (dQ A j x) := fun s => by
  rw [dQ_apply]
  exact Submodule.sum_mem _ fun i _ => (a.S _).toAddSubgroup.zsmul_mem (a.map_mem _ (hx _)) _

def cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) : CH.Cn (sq a b) j :=
  fun s => sqMk a b (val x s) (hx s)

theorem cl_val (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) (s : ComposableArrows C j) :
    (show sqM a b _ from cl a b x hx s).1 = Ideal.Quotient.mk _ (val x s) := rfl

theorem cl_surj (a b : IdF A) {j : ℕ} (f : CH.Cn (sq a b) j) : ∃ (x : Q A j) (hx : Vals a x), cl a b x hx = f := by
  have h : ∀ s : ComposableArrows C j, ∃ x : A.obj (s.obj (Fin.last j)), ∃ hx : x ∈ a.S _, sqMk a b x hx = f s := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, Subtype.ext e⟩
  choose x hx e using h
  exact ⟨x, hx, funext e⟩

theorem cl_eq_zero (a b : IdF A) {j : ℕ} {x : Q A j} {hx : Vals a x} (h : cl a b x hx = 0) : Vals b x := fun s => by
  have h1 := congrArg (fun g : CH.Cn (sq a b) j => (show sqM a b _ from g s).1) h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem d_cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) :
    CH.d (sq a b) j (cl a b x hx) = cl a b (dQ A j x) hx.dQ := by
  funext s
  apply Subtype.ext
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s)) (sqMk a b (val x (face i s)) (hx _)) :
    sqM a b _) = Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)))
  rw [map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

theorem cl_sub (a b : IdF A) {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) :
    cl a b (x - y) (hx.sub hy) = cl a b x hx - cl a b y hy := by
  funext s
  apply Subtype.ext
  exact map_sub (Ideal.Quotient.mk _) _ _

theorem d_cl_zero (a b : IdF A) {j : ℕ} {z : Q A j} (hz : Vals a z) (hd : dQ A j z = 0) :
    CH.d (sq a b) j (cl a b z hz) = 0 := by
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ A j z) s) = 0
  rw [hd]
  exact map_zero (Ideal.Quotient.mk _)

theorem step_zero (a b : IdF A) (h : Subsingleton (CH.H (sq a b) 0)) {z : Q A 0} (hz : Vals a z)
    (hd : dQ A 0 z = 0) : Vals b z := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  exact cl_eq_zero a b ((CechClassBoundaries.class_zero_eq_zero_iff _ _).1 h0)

theorem step_succ (a b : IdF A) {n : ℕ} (h : Subsingleton (CH.H (sq a b) (n + 1))) {z : Q A (n + 1)} (hz : Vals a z)
    (hd : dQ A (n + 1) z = 0) : ∃ y : Q A n, Vals a y ∧ Vals b (z - dQ A n y) := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  obtain ⟨f, hf⟩ := (CechClassBoundaries.mem_Bs _).1 ((CechClassBoundaries.cls_eq_zero _ _).1 h0)
  obtain ⟨y, hy, rfl⟩ := cl_surj a b f
  refine ⟨y, hy, cl_eq_zero a b (hx := hz.sub hy.dQ) ?_⟩
  rw [cl_sub a b hz hy.dQ, ← d_cl a b y hy]
  exact sub_eq_zero.2 hf.symm

abbrev St (a : ℕ → IdF A) (n k : ℕ) : Type 1 := {z : Q A (n + 1) // Vals (a k) z ∧ dQ A (n + 1) z = 0}

theorem exists_seq (a : ℕ → IdF A) {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ y : ℕ → Q A n, (∀ k, Vals (a k) (y k)) ∧
      ∀ k, Vals (a k) (z - dQ A n (∑ i ∈ Finset.range k, y i)) := by
  have hs : ∀ (k : ℕ) (w : St a n k), ∃ y : Q A n, Vals (a k) y ∧ Vals (a (k + 1)) (w.1 - dQ A n y) :=
    fun k w => step_succ _ _ (h k) w.2.1 w.2.2
  choose f hf hg using hs
  let w : ∀ k, St a n k := fun k => Nat.rec ⟨z, hz, hd⟩ (fun k wk => ⟨wk.1 - dQ A n (f k wk), hg k wk, by
    have e : dQ A (n + 1) (dQ A n (f k wk)) = 0 := CH.d_d _ _ _
    rw [map_sub, wk.2.2, e, sub_zero]⟩) k
  refine ⟨fun k => f k (w k), fun k => hf k (w k), fun k => ?_⟩
  have e : ∀ k, (w k).1 = z - dQ A n (∑ i ∈ Finset.range k, f i (w i)) := by
    intro k
    induction k with
    | zero => simp [w]
    | succ k ih =>
      rw [Finset.sum_range_succ, map_add, ← sub_sub, ← ih]
  rw [← e]
  exact (w k).2.1

theorem exists_primitive (a : ℕ → IdF A) (ha : ∀ k T, (a (k + 1)).S T ≤ (a k).S T) (he : ∀ T, ∃ k, (a k).S T = ⊥)
    {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ Y : Q A n, Vals (a 0) Y ∧ z = dQ A n Y := by
  classical
  have hle : ∀ {k m : ℕ}, k ≤ m → ∀ T, (a m).S T ≤ (a k).S T := by
    intro k m hkm T
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact (ha m T).trans ih
  choose K hK using he
  have hbot : ∀ (T : C) {m : ℕ}, K T ≤ m → (a m).S T = ⊥ := fun T m hm =>
    le_bot_iff.1 ((hle hm T).trans (hK T).le)
  obtain ⟨y, hy, hz'⟩ := exists_seq a h hz hd
  let P : ℕ → Q A n := fun N => ∑ i ∈ Finset.range N, y i
  have hP : ∀ (s : ComposableArrows C n) {N : ℕ}, K (s.obj (Fin.last n)) ≤ N →
      val (P N) s = val (P (K (s.obj (Fin.last n)))) s := by
    intro s N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have h0 : val (y m) s = 0 := by
        have := hy m s
        rwa [hbot _ hm, Ideal.mem_bot] at this
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e, h0, add_zero, ih]
  let Y : Q A n := fun s => val (P (K (s.obj (Fin.last n)))) s
  have hP0 : ∀ N, Vals (a 0) (P N) := by
    intro N
    induction N with
    | zero => intro s; simp only [P, Finset.range_zero, Finset.sum_empty]; exact (a 0 |>.S _).zero_mem
    | succ m ih =>
      intro s
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e]
      exact (a 0 |>.S _).add_mem (ih s) (hle (Nat.zero_le m) _ (hy m s))
  refine ⟨Y, fun s => hP0 _ s, ?_⟩
  funext s
  let N : ℕ := max (K (s.obj (Fin.last (n + 1)))) (Finset.univ.sup fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n)))
  have h1 : val (z - dQ A n (P N)) s = 0 := by
    have := hz' N s
    rwa [hbot _ (le_max_left _ _), Ideal.mem_bot] at this
  have h2 : val (dQ A n (P N)) s = val (dQ A n Y) s := by
    rw [dQ_apply, dQ_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP (face i s) ((Finset.le_sup (f := fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n))) (Finset.mem_univ i)).trans (le_max_right _ _))]
  have h3 : val z s = val (dQ A n (P N)) s := sub_eq_zero.1 h1
  exact h3.trans h2

end GlobalTheory.CompanionTheory.TowerEnd

open GlobalTheory.CompanionTheory.TowerEnd in

theorem GlobalTheory.CompanionTheory.TowerEnd.vanish {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A) :
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  intro ha he h j
  have key : ∀ x : CH.H (sq (a 0) (IdF.bot A)) j, x = 0 := by
    intro x
    obtain ⟨f, hf, rfl⟩ := CechClassBoundaries.clsSurj x
    obtain ⟨z, hz, rfl⟩ := cl_surj _ _ f
    have hd : dQ A j z = 0 := by
      rw [d_cl] at hf
      funext s
      exact cl_eq_zero _ _ hf s
    cases j with
    | zero =>
      have hall : ∀ k, Vals (a k) z := by
        intro k
        induction k with
        | zero => exact hz
        | succ k ih => exact step_zero _ _ (h k 0) ih hd
      have h0 : cl (a 0) (IdF.bot A) z hz = 0 := by
        funext s
        obtain ⟨k, hk⟩ := he (s.obj (Fin.last 0))
        have h1 := hall k s
        rw [hk, Ideal.mem_bot] at h1
        apply Subtype.ext
        change Ideal.Quotient.mk _ (val z s) = 0
        rw [h1]
        exact map_zero (Ideal.Quotient.mk _)
      exact (CechClassBoundaries.class_zero_eq_zero_iff _ _).2 h0
    | succ n =>
      obtain ⟨Y, hY, e⟩ := exists_primitive a ha he (fun k => h k (n + 1)) hz hd
      refine (CechClassBoundaries.cls_eq_zero _ _).2 ((CechClassBoundaries.mem_Bs _).2 ⟨cl _ _ Y hY, ?_⟩)
      rw [d_cl]
      subst e
      rfl
  exact ⟨fun x y => (key x).trans (key y).symm⟩
