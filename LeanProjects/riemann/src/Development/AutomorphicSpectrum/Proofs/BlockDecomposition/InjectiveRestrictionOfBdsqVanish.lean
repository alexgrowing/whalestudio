import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.InjRL

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

def wP {n : ℕ} (l : Lt n) : ℕ := n - ((l.2.1.2 : ℕ) - (l.2.1.1 : ℕ))

def potL {n : ℕ} (B : Finset (Lt n)) : ℕ := ∑ l ∈ B, wP l

def pPart {n : ℕ} (A : Finset (Lt n)) : Finset (Lt n) := A.filter fun l => l.1 = true

section Alg

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annL l x A = if l ∈ A then 0 else sgL l A • x (insert l A) := rfl

theorem creL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creL l x A = if l ∈ A then sgL l A • x (A.erase l) else 0 := rfl

theorem liftL_apply (T : V →ₗ[ℂ] V) (x : Cq n V) (A : Finset (Lt n)) : liftL n T x A = T (x A) := rfl

theorem FtL_apply (E1 E2 : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cq n V) (A : Finset (Lt n)) :
    FtL E1 E2 c x A = kA E1 E2 c c (x A) + (wtL A c : ℂ) • x A := rfl

abbrev TriL (S : Lt n → Prop) (l m k : Lt n) : Prop :=
  S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2

open Classical in
theorem bdL_apply (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Cq n V) (A : Finset (Lt n)) :
    bdL S E1 E2 x A = (∑ l : Lt n, if S l then xL E1 E2 l (annL l x A) else 0) +
      ∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n, if TriL S l m k then creL k (annL m (annL l x)) A else 0 := by
  simp only [bdL, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> rfl
  · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> rfl

theorem annL_ne {l : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annL l x A ≠ 0) : l ∉ A ∧ x (insert l A) ≠ 0 := by
  rw [annL_apply] at h
  by_cases hi : l ∈ A
  · simp [hi] at h
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩

theorem creL_ne {l : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL l x A ≠ 0) : l ∈ A ∧ x (A.erase l) ≠ 0 := by
  rw [creL_apply] at h
  by_cases hi : l ∈ A
  · exact ⟨hi, fun h0 => h (by simp [h0])⟩
  · simp [hi] at h

theorem triL_ne {l m k : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL k (annL m (annL l x)) A ≠ 0) :
    k ∈ A ∧ m ∉ A.erase k ∧ l ∉ insert m (A.erase k) ∧ x (insert l (insert m (A.erase k))) ≠ 0 :=
  let h1 := creL_ne h
  let h2 := annL_ne h1.2
  let h3 := annL_ne h2.2
  ⟨h1.1, h2.1, h3.1, h3.2⟩

theorem bdL_sub_ne {S S' : Lt n → Prop} (h0 : ∀ l, S' l → S l) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (x : Cq n V) (A : Finset (Lt n)) (h : bdL S E1 E2 x A ≠ bdL S' E1 E2 x A) :
    (∃ l, S l ∧ ¬S' l ∧ annL l x A ≠ 0) ∨
      ∃ l m k, TriL S l m k ∧ ¬(S' l ∧ S' m) ∧ creL k (annL m (annL l x)) A ≠ 0 := by
  classical
  by_contra hc
  push Not at hc
  apply h
  rw [bdL_apply, bdL_apply]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : S' l
    · rw [if_pos h1, if_pos (h0 _ h1)]
    · rw [if_neg h1]
      split_ifs with h2
      · rw [hc.1 l h2 h1, map_zero]
      · rfl
  · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : TriL S' l m k
    · rw [if_pos h1, if_pos ⟨h0 _ h1.1, h0 _ h1.2.1, h1.2.2⟩]
    · rw [if_neg h1]
      split_ifs with h2
      · exact hc.2 l m k h2 fun a b => h1 ⟨a, b, h2.2.2⟩
      · rfl

theorem bdL_ne (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Cq n V) (A : Finset (Lt n))
    (h : bdL S E1 E2 x A ≠ 0) :
    (∃ l, S l ∧ annL l x A ≠ 0) ∨ ∃ l m k, TriL S l m k ∧ creL k (annL m (annL l x)) A ≠ 0 := by
  classical
  by_contra hc
  push Not at hc
  apply h
  rw [bdL_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · refine fun l _ => Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h2
    · exact hc.2 l m k h2
    · rfl
  · intro l _
    split_ifs with h2
    · rw [hc.1 l h2, map_zero]
    · rfl

theorem pPart_insert (l : Lt n) (A : Finset (Lt n)) :
    pPart (insert l A) = if l.1 = true then insert l (pPart A) else pPart A := filter_insert _ _ _

theorem pPart_erase_of_not {k : Lt n} (hk : ¬k.1 = true) (A : Finset (Lt n)) : pPart (A.erase k) = pPart A := by
  ext a
  simp only [pPart, mem_filter, mem_erase]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun e => hk (e ▸ h.2), h.1⟩, h.2⟩⟩

theorem potL_insert {l : Lt n} {B : Finset (Lt n)} (h : l ∉ B) : potL (insert l B) = wP l + potL B :=
  Finset.sum_insert h

theorem degL_bdL (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Cq n V}
    (hx : DegL (j + 1) x) : DegL j (bdL S E1 E2 x) := by
  intro A hA
  rcases bdL_ne S E1 E2 x A hA with ⟨l, -, h1⟩ | ⟨l, m, k, -, h1⟩
  · obtain ⟨h2, h3⟩ := annL_ne h1
    have := hx _ h3
    rw [card_insert_of_notMem h2] at this
    omega
  · obtain ⟨h2, h3, h4, h5⟩ := triL_ne h1
    have := hx _ h5
    rw [card_insert_of_notMem h4, card_insert_of_notMem h3] at this
    have := card_erase_add_one h2
    omega

theorem partL_bdK (E1 E2 : Fin n → Fin n → Module.End ℂ V) {B : Finset (Lt n)} {x : Cq n V} (hx : PartL B x) :
    PartL B (bdL isK E1 E2 x) := by
  intro A hA
  rcases bdL_ne isK E1 E2 x A hA with ⟨l, hl, h1⟩ | ⟨l, m, k, ht, h1⟩
  · obtain ⟨-, h3⟩ := annL_ne h1
    have e : pPart (insert l A) = B := hx _ h3
    rw [pPart_insert, if_neg (by simp [show l.1 = false from hl])] at e
    exact e
  · obtain ⟨-, -, -, h5⟩ := triL_ne h1
    have e : pPart (insert l (insert m (A.erase k))) = B := hx _ h5
    have hl : l.1 = false := ht.1
    have hm : m.1 = false := ht.2.1
    have hk : k.1 = false := by rw [ht.2.2.2.1, hl, hm]; rfl
    rw [pPart_insert, if_neg (by simp [hl]), pPart_insert, if_neg (by simp [hm]),
      pPart_erase_of_not (by simp [hk])] at e
    exact e

theorem suppL_bdL {S : Lt n → Prop}
    (hS : ∀ l m k : Lt n, S l → S m → l.2.1.2 = m.2.1.1 → k.1 = xor l.1 m.1 → k.2.1 = (l.2.1.1, m.2.1.2) → S k)
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) {x : Cq n V} (hx : SuppL S x) : SuppL S (bdL S E1 E2 x) := by
  intro A hA e he
  rcases bdL_ne S E1 E2 x A hA with ⟨l, -, h1⟩ | ⟨l, m, k, ht, h1⟩
  · exact hx _ (annL_ne h1).2 e (mem_insert_of_mem he)
  · have h5 := (triL_ne h1).2.2.2
    by_cases hk : e = k
    · subst hk
      exact hS l m e (hx _ h5 l (mem_insert_self _ _)) (hx _ h5 m (mem_insert_of_mem (mem_insert_self _ _))) ht.2.2.1
        ht.2.2.2.1 (Prod.ext ht.2.2.2.2.1 ht.2.2.2.2.2)
    · exact hx _ h5 e (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, he⟩)))

theorem pot_lt (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {B : Finset (Lt n)} {x : Cq n V}
    (hx : PartL B x) (A : Finset (Lt n)) (hA : (bdL (inRR lev) E1 E2 x - bdL isK E1 E2 x) A ≠ 0) :
    potL (pPart A) < potL B := by
  have hne : bdL (inRR lev) E1 E2 x A ≠ bdL isK E1 E2 x A := fun h => hA (by
    rw [Pi.sub_apply, h, sub_self])
  have hpos : ∀ l : Lt n, (l.2.1.1 : ℕ) < l.2.1.2 ∧ (l.2.1.2 : ℕ) < n := fun l => ⟨l.2.2, l.2.1.2.2⟩
  rcases bdL_sub_ne (S := inRR lev) (S' := isK) (fun _ h => Or.inl h) E1 E2 x A hne with
    ⟨l, -, h2, h3⟩ | ⟨l, m, k, ht, h2, h3⟩
  · obtain ⟨h4, h5⟩ := annL_ne h3
    have e1 : pPart (insert l A) = B := hx _ h5
    have hl : l.1 = true := by simpa [isK] using h2
    rw [pPart_insert, if_pos hl] at e1
    rw [← e1, potL_insert (B := pPart A) (fun h => h4 (mem_filter.1 h).1)]
    have := hpos l
    simp only [wP]
    omega
  · obtain ⟨h4, h5, h6, h7⟩ := triL_ne h3
    have e1 : pPart (insert l (insert m (A.erase k))) = B := hx _ h7
    obtain ⟨-, -, t1, t0, t2, t3⟩ := ht
    have pl := hpos l
    have pm := hpos m
    have pk := hpos k
    have v1 : (l.2.1.2 : ℕ) = m.2.1.1 := congrArg Fin.val t1
    have v2 : (k.2.1.1 : ℕ) = l.2.1.1 := congrArg Fin.val t2
    have v3 : (k.2.1.2 : ℕ) = m.2.1.2 := congrArg Fin.val t3
    set R := pPart (A.erase k) with hR
    have hmR : m ∉ R := fun h => h5 (mem_filter.1 h).1
    have hlR : l ∉ R := fun h => h6 (mem_insert_of_mem (mem_filter.1 h).1)
    have hlm : l ∉ insert m R := fun h => h6 (by
      rcases mem_insert.1 h with h | h
      · exact h ▸ mem_insert_self _ _
      · exact absurd h hlR)
    have hkR : k ∉ R := fun h => notMem_erase k A (mem_filter.1 h).1
    have hA' : pPart A = if k.1 = true then insert k R else R := by
      conv_lhs => rw [← insert_erase h4, pPart_insert]
    rw [pPart_insert, pPart_insert, ← hR] at e1
    rw [hA', ← e1]
    cases hl : l.1 <;> cases hm : m.1
    · exact absurd ⟨hl, hm⟩ h2
    · have hk : k.1 = true := by rw [t0, hl, hm]; rfl
      simp only [hk, if_true, Bool.false_eq_true, if_false]
      rw [potL_insert hkR, potL_insert hmR]
      simp only [wP]
      omega
    · have hk : k.1 = true := by rw [t0, hl, hm]; rfl
      simp only [hk, if_true, Bool.false_eq_true, if_false]
      rw [potL_insert hkR, potL_insert hlR]
      simp only [wP]
      omega
    · have hk : k.1 = false := by rw [t0, hl, hm]; rfl
      simp only [hk, if_true, Bool.false_eq_true, if_false]
      rw [potL_insert hlm, potL_insert hmR]
      simp only [wP]
      omega

def alL (l : Lt n) (c : Fin n) : ℝ := (if l.2.1.1 = c then 1 else 0) - (if l.2.1.2 = c then 1 else 0)

theorem wtL_insert {l : Lt n} {A : Finset (Lt n)} (h : l ∉ A) (c : Fin n) :
    wtL (insert l A) c = wtL A c + alL l c := by
  simp only [wtL, alL, filter_insert]
  have h1 : ∀ p : Lt n → Prop, ∀ [DecidablePred p], l ∉ A.filter p := fun p _ hh => h (mem_filter.1 hh).1
  split_ifs <;> (try simp only [card_insert_of_notMem (h1 _)]) <;> push_cast <;> ring

theorem FtL_ann (E1 E2 : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (l : Lt n) (x : Cq n V) :
    FtL E1 E2 c (annL l x) = annL l (FtL E1 E2 c x) - (alL l c : ℂ) • annL l x := by
  funext A
  simp only [FtL_apply, annL_apply, Pi.sub_apply, Pi.smul_apply]
  by_cases h : l ∈ A
  · simp [h]
  · rw [if_neg h, if_neg h, wtL_insert h, map_smul]
    push_cast
    module

theorem FtL_cre (E1 E2 : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (l : Lt n) (x : Cq n V) :
    FtL E1 E2 c (creL l x) = creL l (FtL E1 E2 c x) + (alL l c : ℂ) • creL l x := by
  funext A
  simp only [FtL_apply, creL_apply, Pi.add_apply, Pi.smul_apply]
  by_cases h : l ∈ A
  · have e : wtL A c = wtL (A.erase l) c + alL l c := by
      conv_lhs => rw [← insert_erase h]
      exact wtL_insert (notMem_erase l A) c
    rw [if_pos h, if_pos h, e, map_smul]
    push_cast
    module
  · simp [h]

theorem gl_diag {F : Fin n → Fin n → Module.End ℂ V} (h : Formalism.REAL.GlRel F) {a b : Fin n} (hab : a ≠ b) (c : Fin n)
    (x : V) : F c c (F a b x) = F a b (F c c x) +
      ((((if a = c then 1 else 0) - (if b = c then 1 else 0) : ℝ)) : ℂ) • F a b x := by
  have := LinearMap.congr_fun (h c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [sub_eq_iff_eq_add.1 this]
  by_cases h1 : c = a
  · subst h1
    simp [hab.symm, hab]
    abel
  · by_cases h2 : b = c
    · subst h2
      simp [hab, Ne.symm hab]
      abel
    · simp [h1, h2, Ne.symm h1]

theorem kA_xL {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPairA E1 E2) (l : Lt n) (c : Fin n) (x : V) :
    kA E1 E2 c c (xL E1 E2 l x) = xL E1 E2 l (kA E1 E2 c c x) + (alL l c : ℂ) • xL E1 E2 l x := by
  have hne : l.2.1.1 ≠ l.2.1.2 := l.2.2.ne
  have g1 := gl_diag hP.1 hne c x
  have g2 := gl_diag hP.2.1 hne c x
  have c1 : E1 c c (E2 l.2.1.1 l.2.1.2 x) = E2 l.2.1.1 l.2.1.2 (E1 c c x) :=
    LinearMap.congr_fun (hP.2.2 c c l.2.1.1 l.2.1.2) x
  have c2 : E2 c c (E1 l.2.1.1 l.2.1.2 x) = E1 l.2.1.1 l.2.1.2 (E2 c c x) :=
    (LinearMap.congr_fun (hP.2.2 l.2.1.1 l.2.1.2 c c) x).symm
  simp only [xL, alL]
  cases hl : l.1
  · simp only [kA, pA, Bool.false_eq_true, if_false, LinearMap.add_apply, map_add]
    rw [g1, g2, c1, c2]
    module
  · simp only [kA, pA, if_true, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub]
    rw [g1, g2, c1, c2]
    module

theorem ftL_bdL {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPairA E1 E2) (S : Lt n → Prop) (c : Fin n) :
    Commute (FtL E1 E2 c) (bdL S E1 E2) := by
  classical
  unfold bdL
  refine Commute.add_right (Commute.sum_right _ _ _ fun l _ => ?_) (Commute.sum_right _ _ _ fun l _ =>
    Commute.sum_right _ _ _ fun m _ => Commute.sum_right _ _ _ fun k _ => ?_)
  · split_ifs with hi
    · refine LinearMap.ext fun x => ?_
      have e : ∀ y : Cq n V, FtL E1 E2 c (liftL n (xL E1 E2 l) y) =
          liftL n (xL E1 E2 l) (FtL E1 E2 c y) + (alL l c : ℂ) • liftL n (xL E1 E2 l) y := by
        intro y
        funext A
        simp only [FtL_apply, liftL_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul, kA_xL hP]
        module
      simp only [Module.End.mul_apply]
      rw [e, FtL_ann, map_sub, map_smul, sub_add_cancel]
    · exact Commute.zero_right _
  · split_ifs with ht
    · refine LinearMap.ext fun x => ?_
      simp only [Module.End.mul_apply]
      rw [FtL_cre, FtL_ann, FtL_ann]
      have : (alL k c : ℂ) = alL l c + alL m c := by
        rw [← Complex.ofReal_add]
        simp only [alL, ht.2.2.2.2.1, ht.2.2.2.2.2, ht.2.2.1]
        congr 1
        ring
      simp only [map_sub, map_smul, this]
      module
    · exact Commute.zero_right _

theorem wtL_omN (n : ℕ) : wtL (omN n) = (2 : ℝ) • rhoV n := by
  funext c
  have h1 : ((omN n).filter fun l => l.2.1.1 = c).card = (Ioi c).card := by
    refine card_bij (fun l _ => l.2.1.2) (fun l hl => ?_) (fun l hl m hm h => ?_) (fun b hb => ?_)
    · exact mem_Ioi.2 ((mem_filter.1 hl).2 ▸ l.2.2)
    · have a1 := (mem_filter.1 hl).2
      have a2 := (mem_filter.1 hm).2
      have a3 := (mem_filter.1 (mem_filter.1 hl).1).2
      have a4 := (mem_filter.1 (mem_filter.1 hm).1).2
      exact Prod.ext (a3.trans a4.symm) (Subtype.ext (Prod.ext (a1.trans a2.symm) h))
    · exact ⟨(false, ⟨(c, b), mem_Ioi.1 hb⟩), by simp [omN], rfl⟩
  have h2 : ((omN n).filter fun l => l.2.1.2 = c).card = (Iio c).card := by
    refine card_bij (fun l _ => l.2.1.1) (fun l hl => ?_) (fun l hl m hm h => ?_) (fun b hb => ?_)
    · exact mem_Iio.2 ((mem_filter.1 hl).2 ▸ l.2.2)
    · have a1 := (mem_filter.1 hl).2
      have a2 := (mem_filter.1 hm).2
      have a3 := (mem_filter.1 (mem_filter.1 hl).1).2
      have a4 := (mem_filter.1 (mem_filter.1 hm).1).2
      exact Prod.ext (a3.trans a4.symm) (Subtype.ext (Prod.ext h (a1.trans a2.symm)))
    · exact ⟨(false, ⟨(b, c), mem_Iio.1 hb⟩), by simp [omN], rfl⟩
  have h3 : (Ioi c).card + (c : ℕ) + 1 = n := by
    have := c.2
    rw [Fin.card_Ioi]
    omega
  have h4 : (((Ioi c).card : ℕ) : ℝ) + (c : ℕ) + 1 = n := by exact_mod_cast h3
  simp only [wtL, Pi.smul_apply, smul_eq_mul, rhoV]
  rw [h1, h2, Fin.card_Iio, ← h4]
  ring

theorem kA_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPairA E1 E2) (c d : Fin n) (v : V) :
    kA E1 E2 c c (kA E1 E2 d d v) = kA E1 E2 d d (kA E1 E2 c c v) := by
  have g : ∀ {F : Fin n → Fin n → Module.End ℂ V}, Formalism.REAL.GlRel F → ∀ v, F c c (F d d v) = F d d (F c c v) := by
    intro F h v
    have := LinearMap.congr_fun (h c c d d) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    by_cases hcd : c = d
    · subst hcd; rfl
    · rw [if_neg hcd, if_neg (Ne.symm hcd)] at this
      simpa [sub_eq_zero] using this
  have c1 : ∀ v, E1 c c (E2 d d v) = E2 d d (E1 c c v) := fun v => LinearMap.congr_fun (hP.2.2 c c d d) v
  have c2 : ∀ v, E1 d d (E2 c c v) = E2 c c (E1 d d v) := fun v => LinearMap.congr_fun (hP.2.2 d d c c) v
  simp only [kA, LinearMap.add_apply, map_add, g hP.1, g hP.2.1, c1, c2]
  abel

theorem FtL_commute {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPairA E1 E2) (c d : Fin n) :
    Commute (FtL E1 E2 c) (FtL E1 E2 d) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, FtL_apply, map_add, map_smul, kA_comm hP c d, smul_add, smul_smul,
    mul_comm (wtL A c : ℂ)]
  abel

theorem chainL_mem_iSup (E1 E2 : Fin n → Fin n → Module.End ℂ V) (c : Fin n)
    (h : ∀ v : V, v ∈ ⨆ μ : ℂ, (kA E1 E2 c c).eigenspace μ) (t : Cq n V) :
    t ∈ ⨆ μ : ℂ, (FtL E1 E2 c).eigenspace μ := by
  classical
  rw [← Finset.univ_sum_single t]
  refine Submodule.sum_mem _ fun A _ => ?_
  have hle : (⨆ μ : ℂ, (kA E1 E2 c c).eigenspace μ).map (LinearMap.single ℂ (fun _ : Finset (Lt n) => V) A) ≤
      ⨆ μ : ℂ, (FtL E1 E2 c).eigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_le fun μ => le_trans ?_ (le_iSup _ (μ + (wtL A c : ℂ)))
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Module.End.mem_eigenspace_iff.1 hy
    rw [Module.End.mem_eigenspace_iff]
    funext B
    rw [FtL_apply]
    by_cases hB : B = A
    · subst hB
      simp [hy', add_smul]
    · simp [Pi.single_eq_of_ne hB]
  exact hle ⟨t A, h _, rfl⟩

end Alg

theorem wtProjL {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPairA E1 E2)
    (hU : ∀ c (x y : V), inner ℂ (kA E1 E2 c c x) y = inner ℂ x (kA E1 E2 c c y))
    (hL : ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ c, ∀ w ∈ S, kA E1 E2 c c w ∈ S)
    (D : Module.End ℂ (Cq n V)) (hD : ∀ c, Commute (FtL E1 E2 c) D) (τ : Fin n → ℝ) (t : Cq n V)
    (ht : WtL E1 E2 τ (D t)) : ∃ t' : Cq n V, WtL E1 E2 τ t' ∧ D t' = D t ∧ ∀ A, t A = 0 → t' A = 0 := by
  have hdiag : ∀ c (x : Cq n V), x ∈ ⨆ μ : ℂ, (FtL E1 E2 c).eigenspace μ := fun c =>
    chainL_mem_iSup E1 E2 c fun v => by
      obtain ⟨S, hS, hv, hst⟩ := hL v
      haveI := hS
      exact GlobalTheory.CompanionTheory.LKWtProj.mem_iSup_eigenspace (kA E1 E2 c c) (fun x y => hU c x y) S (hst c) v hv
  let W : Submodule ℂ (Cq n V) :=
    { carrier := {x | ∀ A, t A = 0 → x A = 0}
      add_mem' := fun {a b} ha hb A hA => by simp [ha A hA, hb A hA]
      zero_mem' := fun A _ => rfl
      smul_mem' := fun c a ha A hA => by simp [ha A hA] }
  have hW : ∀ c, ∀ x ∈ W, FtL E1 E2 c x ∈ W := fun c x hx A hA => by
    have : x A = 0 := hx A hA
    rw [FtL_apply, this]; simp
  have key : ∀ s : Finset (Fin n), ∃ t' : Cq n V, (∀ c ∈ s, FtL E1 E2 c t' = (τ c : ℂ) • t') ∧ D t' = D t ∧
      t' ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨t, by simp, rfl, fun A hA => hA⟩
    | insert c s _ ih =>
      obtain ⟨u, hu1, hu2, hu3⟩ := ih
      obtain ⟨P, hP1, hP2, hP3, hP4⟩ := GlobalTheory.CompanionTheory.LKWtProj.exists_proj (FtL E1 E2 c) (τ c) u (hdiag c u)
      refine ⟨P u, fun d hd => ?_, ?_, hP2 W (hW c) u hu3⟩
      · rcases Finset.mem_insert.1 hd with rfl | hd
        · exact hP4
        · have := LinearMap.congr_fun (hP1 _ (FtL_commute hP c d)).eq u
          simp only [Module.End.mul_apply] at this
          rw [← this, hu1 d hd, map_smul]
      · have := LinearMap.congr_fun (hP1 _ (hD c)).eq u
        simp only [Module.End.mul_apply] at this
        rw [← this, hu2, hP3 _ (ht c)]
  obtain ⟨t', h1, h2, h3⟩ := key univ
  exact ⟨t', fun c => h1 c (mem_univ c), h2, h3⟩

theorem inRR_closed {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (l m k : Lt n) (hl : inRR lev l) (hm' : inRR lev m)
    (e : l.2.1.2 = m.2.1.1) (e1 : k.1 = xor l.1 m.1) (e2 : k.2.1 = (l.2.1.1, m.2.1.2)) : inRR lev k := by
  have m1 : lev l.2.1.1 ≤ lev l.2.1.2 := hm l.2.2.le
  have m2 : lev m.2.1.1 ≤ lev m.2.1.2 := hm m.2.2.le
  have m3 : lev l.2.1.2 = lev m.2.1.1 := congrArg lev e
  have k1 : k.2.1.1 = l.2.1.1 := (Prod.ext_iff.1 e2).1
  have k2 : k.2.1.2 = m.2.1.2 := (Prod.ext_iff.1 e2).2
  rcases hl with hl | hl
  · rcases hm' with hm' | hm'
    · left; rw [e1, hl, hm']; rfl
    · right; show lev k.2.1.1 < lev k.2.1.2; rw [k1, k2]; omega
  · right
    show lev k.2.1.1 < lev k.2.1.2
    rw [k1, k2]
    rcases hm' with hm' | hm' <;> omega

theorem suppL_sub {n : ℕ} {V : Type} [AddCommGroup V] {P : Lt n → Prop} {x y : Cq n V} (hx : SuppL P x)
    (hy : SuppL P y) : SuppL P (x - y) := by
  intro A hA
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem suppL_sum {n : ℕ} {V : Type} [AddCommGroup V] {ι : Type} {P : Lt n → Prop} (s : Finset ι) (f : ι → Cq n V)
    (h : ∀ b ∈ s, SuppL P (f b)) : SuppL P (∑ b ∈ s, f b) := by
  intro A hA
  rw [Finset.sum_apply] at hA
  obtain ⟨b, hb, h'⟩ := exists_ne_zero_of_sum_ne_zero hA
  exact h b hb A h'

theorem injRL_of (hB : BdSqL) (hV : VanKL) : InjRL := by
  intro n lam hanti lev hlev V _ _ E1 E2 hA u y hu hS hD hb
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hcl : ∀ l m k : Lt n, inRR lev l → inRR lev m → l.2.1.2 = m.2.1.1 → k.1 = xor l.1 m.1 →
      k.2.1 = (l.2.1.1, m.2.1.2) → inRR lev k := inRR_closed hlev.1
  set τ : Fin n → ℝ := muQ lam lev + (2 : ℝ) • rhoV n with hτ
  have hsq : ∀ x, bdL (inRR lev) E1 E2 (bdL (inRR lev) E1 E2 x) = 0 := fun x =>
    LinearMap.congr_fun (hB n _ hcl V E1 E2 hP) x
  have main : ∀ N (y : Cq n V), (∀ A, y A ≠ 0 → A.card = (omN n).card + 1 ∧ potL (pPart A) < N) →
      SuppL (inRR lev) y → WtL E1 E2 τ y → bdL (inRR lev) E1 E2 y = Pi.single (omN n) u → u = 0 := by
    intro N
    induction N with
    | zero =>
      intro y h _ _ hb
      obtain rfl : y = 0 := funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2
      simpa using (congrFun hb (omN n)).symm
    | succ N ih =>
      intro y h hys hw hb
      let r : Finset (Lt n) → Cq n V := fun B A => if pPart A = B then y A else 0
      have hry : ∀ B A, r B A ≠ 0 → pPart A = B ∧ y A ≠ 0 := fun B A hA => by
        simp only [r] at hA
        split_ifs at hA with h1
        · exact ⟨h1, hA⟩
        · exact absurd rfl hA
      have hr : ∀ B, PartL B (r B) := fun B A hA => (hry B A hA).1
      have hrD : ∀ B, DegL ((omN n).card + 1) (r B) := fun B A hA => (h A (hry B A hA).2).1
      have hsum : y = ∑ B, r B := funext fun A => by simp [r, Finset.sum_apply]
      have hrne : ∀ B A, r B A ≠ 0 → potL B < N + 1 ∧ B.Nonempty ∧ ∀ l ∈ B, l.1 = true ∧ inUU lev l := fun B A hA => by
        obtain ⟨h3, h2⟩ := hry B A hA
        have h4 := h A h2
        refine ⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, fun l hl => ?_⟩
        · have hsub : A ⊆ omN n := fun i hi => mem_filter.2 ⟨mem_univ _, by
            by_contra hc
            have : i ∈ pPart A := mem_filter.2 ⟨hi, by simpa using hc⟩
            rw [h3, hB] at this
            exact notMem_empty i this⟩
          have := card_le_card hsub
          omega
        · rw [← h3] at hl
          obtain ⟨hl1, hl2⟩ := mem_filter.1 hl
          refine ⟨hl2, (hys A h2 l hl1).resolve_left ?_⟩
          rw [hl2]; simp
      have hrw : ∀ B, WtL E1 E2 τ (r B) := fun B c => funext fun A => by
        have := congrFun (hw c) A
        change kA E1 E2 c c (y A) + (wtL A c : ℂ) • y A = (τ c : ℂ) • y A at this
        change kA E1 E2 c c (r B A) + (wtL A c : ℂ) • r B A = (τ c : ℂ) • r B A
        simp only [r]
        split_ifs
        · exact this
        · simp
      have hz : ∀ B, potL B = N → bdL isK E1 E2 (r B) = 0 := by
        intro B hBN
        funext A
        by_contra hne
        have hAB : pPart A = B := partL_bdK E1 E2 (hr B) A hne
        have hr0 : r B ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
        obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 hr0
        obtain ⟨-, hBn, -⟩ := hrne B A₀ hA₀
        have hAo : A ≠ omN n := by
          rintro rfl
          obtain ⟨i, hi⟩ := hBn
          rw [← hAB] at hi
          have h1 := (mem_filter.1 hi).2
          have h2 := (mem_filter.1 (mem_filter.1 hi).1).2
          rw [h1] at h2
          simp at h2
        have e := congrFun hb A
        rw [Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B] at e
        · apply hne
          by_contra h'
          have := pot_lt lev E1 E2 (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 h')
          rw [hAB] at this
          exact lt_irrefl _ this
        · intro B' _ hB'
          by_cases h1 : r B' = 0
          · simp [h1]
          obtain ⟨A₁, hA₁⟩ := Function.ne_iff.1 h1
          have h2 := (hrne B' A₁ hA₁).1
          have h3 : bdL isK E1 E2 (r B') A = 0 := by
            by_contra h3; exact hB' ((partL_bdK E1 E2 (hr B') A h3).symm.trans hAB)
          by_contra h4
          have := pot_lt lev E1 E2 (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)
          rw [hAB] at this
          omega
        · simp
      have hex : ∀ B, ∃ t : Cq n V, WtL E1 E2 τ t ∧ (potL B = N → bdL isK E1 E2 t = r B) ∧ (potL B ≠ N → t = 0) ∧
          (t = 0 ∨ PartL B t) ∧ DegL ((omN n).card + 1 + 1) t ∧ SuppL (inRR lev) t := by
        intro B
        by_cases h0 : potL B = N ∧ r B ≠ 0
        · obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 h0.2
          obtain ⟨-, hBn, hBU⟩ := hrne B A₀ hA₀
          obtain ⟨t, t1, t2, t3, t4⟩ := hV n lam hanti lev hlev V E1 E2 hA B _ (r B) hBn hBU (hr B) (hrD B) (hrw B)
            (hz B h0.1)
          refine ⟨t, t3, fun _ => t4, fun h => absurd h0.1 h, Or.inr t1, t2, fun A hA i hi => ?_⟩
          by_cases hci : i.1 = false
          · exact Or.inl hci
          · have : i ∈ pPart A := mem_filter.2 ⟨hi, by simpa using hci⟩
            have e : pPart A = B := t1 A hA
            rw [e] at this
            exact Or.inr (hBU i this).2
        · refine ⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl, fun A hA => absurd rfl hA,
            fun A hA => absurd rfl hA⟩
          rw [map_zero]
          by_contra h'
          exact h0 ⟨h, Ne.symm h'⟩
      choose t t1 t2 t3 t4 t5d t5 using hex
      refine ih (y - ∑ B, bdL (inRR lev) E1 E2 (t B)) (fun A hA => ?_)
        (suppL_sub hys (suppL_sum _ _ fun B _ => suppL_bdL hcl E1 E2 (t5 B))) (fun c => ?_) ?_
      · have e : (y - ∑ B, bdL (inRR lev) E1 E2 (t B)) A =
            ∑ B, ((if potL B = N then 0 else r B A) - (bdL (inRR lev) E1 E2 (t B) - bdL isK E1 E2 (t B)) A) := by
          rw [Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs with h1
          · rw [Pi.sub_apply, t2 B h1]; abel
          · simp [t3 B h1]
        rw [e] at hA
        obtain ⟨B, -, hB⟩ := exists_ne_zero_of_sum_ne_zero hA
        by_cases h1 : potL B = N
        · rw [if_pos h1, zero_sub, neg_ne_zero] at hB
          rcases t4 B with h2 | h2
          · simp [h2] at hB
          · have h3 := pot_lt lev E1 E2 h2 A hB
            refine ⟨?_, by omega⟩
            rw [Pi.sub_apply] at hB
            by_cases h4 : bdL (inRR lev) E1 E2 (t B) A = 0
            · refine degL_bdL isK E1 E2 (t5d B) A fun h5 => hB (by rw [h4, h5, sub_zero])
            · exact degL_bdL _ E1 E2 (t5d B) A h4
        · rw [if_neg h1, t3 B h1] at hB
          have hB' : r B A ≠ 0 := by simpa using hB
          have h2 := (hrne B A hB').1
          have h3 := (hry B A hB')
          exact ⟨(h A h3.2).1, by rw [h3.1]; omega⟩
      · rw [map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Module.End.mul_apply, (ftL_bdL hP _ c).eq, Module.End.mul_apply, t1 B c, map_smul]
      · rw [map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]
        exact fun B _ => hsq _
  obtain ⟨y', y1, y2, y3⟩ := wtProjL hP (fun c x y => hA.unitK c c x y)
    (fun x => by
      obtain ⟨S, h1, h2, h3⟩ := hA.locFin x
      exact ⟨S, h1, h2, fun c => h3 c c⟩) _ (fun c => ftL_bdL hP _ c) τ y (fun c => funext fun A => by
    rw [hb]
    change kA E1 E2 c c ((Pi.single (omN n) u : Cq n V) A) + (wtL A c : ℂ) • (Pi.single (omN n) u : Cq n V) A =
      (τ c : ℂ) • (Pi.single (omN n) u : Cq n V) A
    by_cases e : A = omN n
    · subst e
      have h1 : kA E1 E2 c c u = (muQ lam lev c : ℂ) • u := hu.1 c
      rw [Pi.single_eq_same, h1, wtL_omN, ← add_smul, hτ]
      simp
    · simp [Pi.single_eq_of_ne e])
  refine main ((univ.sup fun A : Finset (Lt n) => potL A) + 1) y' (fun A hA => ⟨hD A fun h => hA (y3 A h), ?_⟩)
    (fun A hA => hS A fun h => hA (y3 A h)) y1 (y2.trans hb)
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Lt n) => potL A) (mem_univ _))

end GlobalTheory.CompanionTheory.InjRL
