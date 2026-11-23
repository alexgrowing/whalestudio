import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveMV

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def Cob (W : ObjectProperty C) : ∀ j : ℕ, CrystallineSemistableComparison.CH.Cn F j → Prop
  | 0, x => ∀ s : ComposableArrows C 0, W (s.obj 0) → x s = 0
  | j + 1, x => ∃ y : CrystallineSemistableComparison.CH.Cn F j, ∀ s : ComposableArrows C (j + 1), W (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F j y s

def Van (W : ObjectProperty C) (j : ℕ) : Prop :=
  ∀ x : CrystallineSemistableComparison.CH.Cn F j, (∀ s : ComposableArrows C (j + 1), W (s.obj 0) → CrystallineSemistableComparison.CH.d F j x s = 0) → Cob F W j x

variable {F}

theorem face_start {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (i : Fin (n + 2))
    (s : ComposableArrows C (n + 1)) (h : W (s.obj 0)) : W ((face i s).obj 0) :=
  hW (s.map (homOfLE (Fin.zero_le _))) h

theorem d_congr {n : ℕ} (x y : CrystallineSemistableComparison.CH.Cn F n) (s : ComposableArrows C (n + 1))
    (h : ∀ i, x (face i s) = y (face i s)) : CrystallineSemistableComparison.CH.d F n x s = CrystallineSemistableComparison.CH.d F n y s := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (x (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (y (face i s))
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

def liftCh {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (s : ComposableArrows C n) (h : W (s.obj 0)) :
    ComposableArrows W.FullSubcategory n :=
  W.lift s fun i => hW (s.map (homOfLE (Fin.zero_le i))) h

open Classical in

def extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) : CrystallineSemistableComparison.CH.Cn F n :=
  fun s => if h : W (s.obj 0) then y (liftCh hW s h) else 0

theorem pull_extZ {W : ObjectProperty C} (hW : Cosieve W) {n : ℕ} (y : CrystallineSemistableComparison.CH.Cn (W.ι ⋙ F) n) :
    (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC n (extZ hW y) = y := by
  funext t
  have h : W ((t ⋙ W.ι).obj 0) := (t.obj 0).property
  change extZ hW y (t ⋙ W.ι) = y t
  unfold extZ
  rw [dif_pos h]
  rfl

theorem van_of_subsingleton {W : ObjectProperty C} (hW : Cosieve W) (j : ℕ)
    (hs : Subsingleton (HU F W j)) : Van F W j := by
  intro x hx
  have hz : CrystallineSemistableComparison.CH.d (W.ι ⋙ F) j ((CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC j x) = 0 := by
    rw [CrystallineSemistableComparison.CH.Mor.d_pullC]
    funext t
    exact hx (t ⋙ W.ι) (t.obj 0).property
  have hB := ((CrystallineSemistableComparison.P.cls_surj (CrystallineSemistableComparison.CH.cx (W.ι ⋙ F)) j).2.1 _ hz).1 (Subsingleton.elim _ _)
  cases j with
  | zero =>
    intro s h
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC 0 x = 0 := hB
    exact congrFun e (liftCh hW s h)
  | succ j =>
    obtain ⟨y, hy⟩ := hB
    refine ⟨extZ hW y, fun s h => ?_⟩
    have e : (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) x =
        (CrystallineSemistableComparison.CH.Mor.restrict F W.ι).pullC (j + 1) (CrystallineSemistableComparison.CH.d F j (extZ hW y)) := by
      rw [← CrystallineSemistableComparison.CH.Mor.d_pullC, pull_extZ]
      exact hy.symm
    exact congrFun e (liftCh hW s h)

theorem van_sup {U V : ObjectProperty C} (hU : Cosieve U) (hV : Cosieve V) {j : ℕ}
    (h1 : Van F U j) (h2 : Van F V j) (h3 : ∀ i, j = i + 1 → Van F (fun T => U T ∧ V T) i) :
    Van F (fun T => U T ∨ V T) j := by
  intro x hx
  have ca := h1 x fun s h => hx s (Or.inl h)
  have cb := h2 x fun s h => hx s (Or.inr h)
  cases j with
  | zero =>
    rintro s (h | h)
    · exact ca s h
    · exact cb s h
  | succ n =>
    obtain ⟨a, ha⟩ := ca
    obtain ⟨b, hb⟩ := cb
    have hz : ∀ s : ComposableArrows C (n + 1), (U (s.obj 0) ∧ V (s.obj 0)) →
        CrystallineSemistableComparison.CH.d F n (a - b) s = 0 := by
      intro s hs
      rw [map_sub, Pi.sub_apply, ← ha s hs.1, ← hb s hs.2, sub_self]
    have hc := h3 n rfl (a - b) hz
    obtain ⟨a', ha', hab⟩ : ∃ a' : CrystallineSemistableComparison.CH.Cn F n,
        (∀ s : ComposableArrows C (n + 1), U (s.obj 0) → x s = CrystallineSemistableComparison.CH.d F n a' s) ∧
        ∀ s : ComposableArrows C n, U (s.obj 0) → V (s.obj 0) → a' s = b s := by
      cases n with
      | zero => exact ⟨a, ha, fun s h h' => sub_eq_zero.1 (hc s ⟨h, h'⟩)⟩
      | succ m =>
        obtain ⟨c, hc⟩ := hc
        refine ⟨a - CrystallineSemistableComparison.CH.d F m c, fun s h => ?_, fun s h h' => ?_⟩
        · rw [map_sub, CrystallineSemistableComparison.CH.d_d, sub_zero]
          exact ha s h
        · have e := hc s ⟨h, h'⟩
          rw [Pi.sub_apply] at e ⊢
          rw [← e]
          abel
    classical
    refine ⟨fun s => if U (s.obj 0) then a' s else b s, fun s hs => ?_⟩
    by_cases hu : U (s.obj 0)
    · rw [ha' s hu]
      exact d_congr _ _ s fun i => (if_pos (face_start hU i s hu)).symm
    · have hv : V (s.obj 0) := hs.resolve_left hu
      rw [hb s hv]
      refine d_congr _ _ s fun i => ?_
      by_cases hui : U ((face i s).obj 0)
      · exact (hab _ hui (face_start hV i s hv)).symm.trans (if_pos hui).symm
      · exact (if_neg hui).symm

theorem van_congr {W W' : ObjectProperty C} (h : ∀ T, W T ↔ W' T) {j : ℕ} (hv : Van F W j) : Van F W' j := by
  obtain rfl : W = W' := funext fun T => propext (h T)
  exact hv

theorem van_empty {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Van F W j := by
  intro x _
  cases j with
  | zero => exact fun s hs => (h _ hs).elim
  | succ j => exact ⟨0, fun s hs => (h _ hs).elim⟩

def Wc {ι : Type} (U : ι → ObjectProperty C) (A S : Finset ι) : ObjectProperty C :=
  fun T => (∃ α ∈ A, U α T) ∧ capS U S T

theorem cosieve_capS {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (S : Finset ι) :
    Cosieve (capS U S) :=
  fun _ _ f h α hα => hU α f (h α hα)

theorem cosieve_Wc {ι : Type} {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α)) (A S : Finset ι) :
    Cosieve (Wc U A S) := by
  rintro T T' f ⟨⟨α, hα, hT⟩, hS⟩
  exact ⟨⟨α, hα, hU α f hT⟩, cosieve_capS hU S f hS⟩

theorem van_Wc {ι : Type} [DecidableEq ι] {U : ι → ObjectProperty C} (hU : ∀ α, Cosieve (U α))
    (D : ℕ → ℕ → Prop) (E : ℕ → Prop) (hD : ∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i)
    (hcap : ∀ S : Finset ι, S.Nonempty → ∀ j, E j → Van F (capS U S) j) (A : Finset ι) :
    ∀ (S : Finset ι) (j : ℕ), D A.card j → Van F (Wc U A S) j := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j _
    exact van_empty (fun T hT => by simpa using hT.1) j
  | insert a A ha ih =>
    intro S j hj
    rw [Finset.card_insert_of_notMem ha] at hj
    obtain ⟨d1, d2, d3⟩ := hD _ _ hj
    have key := van_sup (cosieve_Wc hU A S) (cosieve_capS hU (insert a S)) (ih S j d1)
      (hcap _ (Finset.insert_nonempty _ _) j d2) fun i hi => van_congr (fun T => ⟨fun h =>
        ⟨⟨h.1, fun α hα => h.2 α (Finset.mem_insert_of_mem hα)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩)
        (ih (insert a S) i (d3 i hi))
    refine van_congr (fun T => ⟨?_, ?_⟩) key
    · rintro (⟨⟨α, hα, hT⟩, hS⟩ | h)
      · exact ⟨⟨α, Finset.mem_insert_of_mem hα, hT⟩, hS⟩
      · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
          fun α hα => h α (Finset.mem_insert_of_mem hα)⟩
    · rintro ⟨⟨α, hα, hT⟩, hS⟩
      rcases Finset.mem_insert.1 hα with rfl | h
      · refine Or.inr fun β hβ => ?_
        rcases Finset.mem_insert.1 hβ with rfl | h'
        · exact hT
        · exact hS β h'
      · exact Or.inl ⟨⟨α, h, hT⟩, hS⟩

theorem subsingleton_of_van {W : ObjectProperty C} (hW : ∀ T, W T) {j : ℕ} (h : Van F W j) :
    Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  refine ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 a ha).2 ?_
  have hc := h a fun s _ => congrFun ha s
  cases j with
  | zero => exact funext fun s => hc s (hW _)
  | succ j =>
    obtain ⟨y, hy⟩ := hc
    exact ⟨y, funext fun s => (hy s (hW _)).symm⟩

theorem vanishing_of_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  intro R _ C _ F ι _ U hU hc s
  classical
  have key : ∀ (D : ℕ → ℕ → Prop) (E : ℕ → Prop),
      (∀ n j, D (n + 1) j → D n j ∧ E j ∧ ∀ i, j = i + 1 → D n i) →
      (∀ S : Finset ι, S.Nonempty → ∀ j, E j → Subsingleton (HU F (capS U S) j)) →
      ∀ j, D (Fintype.card ι) j → Subsingleton (CrystallineSemistableComparison.CH.H F j) := by
    intro D E hD h j hj
    refine subsingleton_of_van (W := Wc U Finset.univ ∅) (fun T => ?_)
      (van_Wc hU D E hD (fun S hS j hE => van_of_subsingleton (cosieve_capS hU S) j (h S hS j hE))
        Finset.univ ∅ j (by simpa using hj))
    obtain ⟨α, hα⟩ := hc T
    exact ⟨⟨α, Finset.mem_univ _, hα⟩, fun β hβ => by simp at hβ⟩
  refine ⟨fun h j hj => key (fun _ j => j < s) (fun j => j < s) ?_ (fun S hS j hE => h S hS j hE) j hj,
    fun h j => key (fun _ _ => True) (fun _ => True) ?_ (fun S hS j _ => h S hS j) j trivial,
    fun h j hj => key (fun n j => s + n ≤ j) (fun j => j > s) ?_ (fun S hS j hE => h S hS j hE) j hj⟩
  · intro n j hj
    exact ⟨hj, hj, fun i hi => by omega⟩
  · intro n j _
    exact ⟨trivial, trivial, fun _ _ => trivial⟩
  · intro n j hj
    exact ⟨by omega, by omega, fun i hi => by omega⟩

end GlobalTheory.CompanionTheory.CosieveMV
