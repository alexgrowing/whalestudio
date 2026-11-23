import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnEqZeroOfDegreeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CreAnnApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BracketLeviModuleBoundaryPart

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.COU

open GlobalTheory.CompanionTheory.PairMult
open CompanionTheory.D.LK (Pos key)
open Formalism.REAL (GlRel)

variable {n : ℕ}
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

structure MorQ (T : V →ₗ[ℂ] W) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (F1 F2 : Fin n → Fin n → Module.End ℂ W) : Prop where
  h1 : ∀ a b y, T (E1 a b y) = F1 a b (T y)
  h2 : ∀ a b y, T (E2 a b y) = F2 a b (T y)

theorem adLq_apply (s : Bool) (p q : Fin n) (x : Cq n V) :
    adLq s p q x = ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n,
      CompanionTheory.RgExh.U.adC p q i k • creq ((s == t), k) (annq (t, i) x) := by
  simp [adLq, Module.End.mul_apply, LinearMap.sum_apply]

theorem lift_adLq (T : V →ₗ[ℂ] W) (s : Bool) (p q : Fin n) (x : Cq n V) :
    liftq n T (adLq s p q x) = adLq s p q (liftq n T x) := by
  simp only [adLq_apply, map_sum, map_smul, lift_cre', lift_ann']

section MorLemmas

variable {T : V →ₗ[ℂ] W} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}

theorem MorQ.Ts_eq (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (y : V) :
    T (Ts E1 E2 s p q y) = Ts F1 F2 s p q (T y) := by
  cases s <;> simp [Ts, h.h1, h.h2]

theorem MorQ.lift_Ts (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (y : Cq n V) :
    liftq n T (liftq n (Ts E1 E2 s p q) y) = liftq n (Ts F1 F2 s p q) (liftq n T y) := by
  funext A
  exact h.Ts_eq s p q (y A)

theorem MorQ.lift_Tl (h : MorQ T E1 E2 F1 F2) (i : Lt n) (y : Cq n V) :
    liftq n T (liftq n (Tl E1 E2 i) y) = liftq n (Tl F1 F2 i) (liftq n T y) :=
  h.lift_Ts _ _ _ y

theorem MorQ.bd (h : MorQ T E1 E2 F1 F2) (x : Cq n V) :
    liftq n T (bdq E1 E2 x) = bdq F1 F2 (liftq n T x) := by
  rw [bd_apply, bd_apply]
  simp only [map_add, map_smul, map_sum, lift_cre', lift_ann', h.lift_Tl]

theorem MorQ.lF (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (x : Cq n V) :
    liftq n T (lFq E1 E2 s p q x) = lFq F1 F2 s p q (liftq n T x) := by
  simp only [lFq, LinearMap.add_apply, map_add, h.lift_Ts, lift_adLq]

theorem MorQ.cc1 (h : MorQ T E1 E2 F1 F2) (p q : Fin n) (x : Cq n V) :
    liftq n T (c1 E1 E2 p q x) = c1 F1 F2 p q (liftq n T x) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, h.lF]

theorem MorQ.cc2 (h : MorQ T E1 E2 F1 F2) (p q : Fin n) (x : Cq n V) :
    liftq n T (c2 E1 E2 p q x) = c2 F1 F2 p q (liftq n T x) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, h.lF]

theorem MorQ.evC (h : MorQ T E1 E2 F1 F2) (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ x : Cq n V, liftq n T (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 F1 F2) (c2 F1 F2) b (liftq n T x) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ x : Cq n V,
    liftq n T (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 F1 F2) (c2 F1 F2) b (liftq n T x)) ?_ ?_ ?_ ?_ b
  · intro r x
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  · intro p x
    simp only [evB, FreeAlgebra.lift_ι_apply]
    split_ifs
    · exact h.cc1 _ _ x
    · exact h.cc2 _ _ x
    · simp
  · intro a b ha hb x
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb x
    simp only [map_add, LinearMap.add_apply, ha, hb]

theorem MorQ.ev (h : MorQ T E1 E2 F1 F2) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ y : V, T (ev2 E1 E2 a y) = ev2 F1 F2 a (T y) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun a => ∀ y : V, T (ev2 E1 E2 a y) = ev2 F1 F2 a (T y)) ?_ ?_ ?_ ?_ a
  · intro r y
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  · intro p y
    simp only [ev2, FreeAlgebra.lift_ι_apply]
    by_cases hp : p.1 = true
    · simp [hp, h.h1]
    · simp [hp, h.h2]
  · intro a b ha hb y
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb y
    simp only [map_add, LinearMap.add_apply, map_add, ha, hb]

theorem MorQ.lift_ev (h : MorQ T E1 E2 F1 F2) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (x : Cq n V) :
    liftq n T (liftq n (ev2 E1 E2 a) x) = liftq n (ev2 F1 F2 a) (liftq n T x) := by
  funext A
  exact h.ev a (x A)

end MorLemmas

theorem evC_facts (hR : LeviRel) {lev : Fin n → ℕ} (hlev : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hE : PairRel E1 E2) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ x : Cq n V, SuppQ (inUL lev) x → SuppQ (inUL lev) (evB lev (c1 E1 E2) (c2 E1 E2) b x) ∧
      (∀ j, DegQ j x → DegQ j (evB lev (c1 E1 E2) (c2 E1 E2) b x)) ∧
      bdq E1 E2 (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 E1 E2) (c2 E1 E2) b (bdq E1 E2 x) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ x : Cq n V, SuppQ (inUL lev) x →
    SuppQ (inUL lev) (evB lev (c1 E1 E2) (c2 E1 E2) b x) ∧
      (∀ j, DegQ j x → DegQ j (evB lev (c1 E1 E2) (c2 E1 E2) b x)) ∧
      bdq E1 E2 (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 E1 E2) (c2 E1 E2) b (bdq E1 E2 x)) ?_ ?_ ?_ ?_ b
  · intro r x hx
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    exact ⟨Submodule.smul_mem (supSub V _) r hx, fun j hj => Submodule.smul_mem (supSub V _) r hj, trivial⟩
  · intro c x hx
    have hs := (hR n lev V E1 E2 hlev hE x hx).1
    simp only [evB, FreeAlgebra.lift_ι_apply]
    by_cases hc : lev c.2.1 = lev c.2.2
    · obtain ⟨t1, t2, t3⟩ := hs true _ _ hc
      obtain ⟨f1, f2, f3⟩ := hs false _ _ hc
      rw [if_pos hc]
      by_cases h1 : c.1 = true
      · simp only [h1, if_true, GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add]
        refine ⟨Submodule.smul_mem (supSub V _) _ (Submodule.add_mem (supSub V _) t1 f1), fun j hj =>
          Submodule.smul_mem (supSub V _) _ (Submodule.add_mem (supSub V _) (t2 j hj) (f2 j hj)), ?_⟩
        rw [t3, f3]
      · simp only [h1, Bool.false_eq_true, if_false, GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, map_smul,
          map_sub]
        refine ⟨Submodule.smul_mem (supSub V _) _ (Submodule.sub_mem (supSub V _) t1 f1), fun j hj =>
          Submodule.smul_mem (supSub V _) _ (Submodule.sub_mem (supSub V _) (t2 j hj) (f2 j hj)), ?_⟩
        rw [t3, f3]
    · rw [if_neg hc]
      simp only [LinearMap.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem (supSub V _), fun j _ => Submodule.zero_mem (supSub V _), trivial⟩
  · intro a b ha hb x hx
    obtain ⟨h1, h2, h3⟩ := hb x hx
    obtain ⟨h4, h5, h6⟩ := ha _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h4, fun j hj => h5 j (h2 j hj), by rw [h6, h3]⟩
  · intro a b ha hb x hx
    obtain ⟨h1, h2, h3⟩ := ha x hx
    obtain ⟨h4, h5, h6⟩ := hb x hx
    simp only [map_add, LinearMap.add_apply]
    exact ⟨Submodule.add_mem (supSub V _) h1 h4, fun j hj => Submodule.add_mem (supSub V _) (h2 j hj) (h5 j hj),
      by rw [h3, h6]⟩

theorem lift_bd_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} {S : Lt n → Prop} {T : Module.End ℂ V}
    (hT : ∀ i, S i → Commute (Tl E1 E2 i) T) {x : Cq n V} (hx : SuppQ S x) :
    liftq n T (bdq E1 E2 x) = bdq E1 E2 (liftq n T x) := by
  rw [bd_apply, bd_apply]
  have hk : ∀ i : Lt n, liftq n T (liftq n (Tl E1 E2 i) (annq i x)) =
      liftq n (Tl E1 E2 i) (annq i (liftq n T x)) := by
    intro i
    by_cases hi : S i
    · funext A
      rw [← lift_ann']
      simp only [lift_apply]
      exact (LinearMap.congr_fun (hT i hi).eq _).symm
    · rw [← lift_ann', ann_zero hx hi]
      simp
  simp only [map_add, map_smul, map_sum, lift_cre', lift_ann' T, hk]

theorem single_degree_zero (v : V) : DegQ 0 (Pi.single ∅ v : Cq n V) := by
  intro A hA
  by_contra h
  have : A ≠ ∅ := fun h0 => h (by simp [h0])
  exact hA (by simp [Pi.single_apply, this])

theorem eq_single {x : Cq n V} (hx : DegQ 0 x) : x = Pi.single ∅ (x ∅) := by
  funext A
  by_cases h : A = ∅
  · subst h
    simp
  · rw [Pi.single_apply, if_neg h]
    by_contra h0
    exact h (card_eq_zero.mp (hx A h0))

theorem lift_single (T : V →ₗ[ℂ] W) (v : V) :
    liftq n T (Pi.single ∅ v : Cq n V) = Pi.single ∅ (T v) := by
  funext A
  by_cases h : A = ∅
  · subst h
    simp [lift_apply]
  · simp [lift_apply, Pi.single_apply, h]

theorem lF_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) (v : V) :
    lFq E1 E2 s p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (Ts E1 E2 s p q v) := by
  rw [lFq, LinearMap.add_apply, lift_single, adLq_apply]
  simp [ann_eq_zero_of_degree_zero _ (single_degree_zero (n := n) v)]

theorem chainOp_apply_single_empty (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (v : V) :
    c1 E1 E2 p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (E1 p q v) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, lF_single, ← Pi.single_add, ← Pi.single_smul]
  congr 1
  simp only [Ts, if_true, Bool.false_eq_true, if_false, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem second_operator_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (v : V) :
    c2 E1 E2 p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (E2 p q v) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, lF_single, ← Pi.single_sub, ← Pi.single_smul]
  congr 1
  simp only [Ts, if_true, Bool.false_eq_true, if_false, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem evC_single (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ v : V, evB lev (c1 E1 E2) (c2 E1 E2) b (Pi.single ∅ v : Cq n V) = Pi.single ∅ (evB lev E1 E2 b v) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ v : V,
    evB lev (c1 E1 E2) (c2 E1 E2) b (Pi.single ∅ v : Cq n V) = Pi.single ∅ (evB lev E1 E2 b v)) ?_ ?_ ?_ ?_ b
  · intro r v
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [Pi.single_smul]
  · intro p v
    simp only [evB, FreeAlgebra.lift_ι_apply]
    split_ifs
    · exact chainOp_apply_single_empty E1 E2 _ _ v
    · exact second_operator_single E1 E2 _ _ v
    · simp
  · intro a b ha hb v
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb v
    simp only [map_add, LinearMap.add_apply, ha, hb, Pi.single_add]

theorem single_one_deg (i : Lt n) (y : V) : DegQ 1 (Pi.single {i} y : Cq n V) := by
  intro A hA
  by_contra h
  have : A ≠ {i} := fun h0 => h (by simp [h0])
  exact hA (by simp [Pi.single_apply, this])

theorem ann_single (k i : Lt n) (y : V) :
    annq k (Pi.single {i} y : Cq n V) = if k = i then Pi.single ∅ y else 0 := by
  funext A
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, ann_apply]
    by_cases hA : k ∈ A
    · have : A ≠ ∅ := fun h0 => by simp [h0] at hA
      simp [hA, Pi.single_apply, this]
    · by_cases h0 : A = ∅
      · subst h0
        simp [sgL]
      · have : insert k A ≠ {k} := by
          intro h
          obtain ⟨l, hl⟩ := nonempty_iff_ne_empty.mpr h0
          have := h ▸ mem_insert_of_mem hl
          rw [mem_singleton] at this
          exact hA (this ▸ hl)
        simp [hA, Pi.single_apply, this, h0]
  · rw [if_neg hk, ann_apply]
    by_cases hA : k ∈ A
    · simp [hA]
    · have : insert k A ≠ {i} := by
        intro h
        have := h ▸ mem_insert_self k A
        exact hk (mem_singleton.mp this)
      simp [hA, Pi.single_apply, this]

theorem bd_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Lt n) (y : V) :
    bdq E1 E2 (Pi.single {i} y : Cq n V) = Pi.single ∅ (Tl E1 E2 i y) := by
  rw [bd_apply]
  have h2 : ∀ i' j k : Lt n, cq i' j k • creq k (annq j (annq i' (Pi.single {i} y : Cq n V))) = 0 := by
    intro i' j k
    rw [ann_eq_zero_of_degree_zero j (ann_deg i' (single_one_deg i y))]
    simp
  simp only [h2, sum_const_zero, smul_zero, add_zero]
  simp only [ann_single]
  rw [Finset.sum_eq_single i]
  · simp [lift_single]
  · intro k _ hk
    simp [hk]
  · simp

theorem single_one_supp {P : Lt n → Prop} {i : Lt n} (hi : P i) (y : V) : SuppQ P (Pi.single {i} y : Cq n V) := by
  intro A hA l hl
  by_cases h : A = {i}
  · subst h
    rw [mem_singleton.1 hl]
    exact hi
  · exact absurd (by simp [Pi.single_apply, h]) hA

theorem gl_of_inj {T : V →ₗ[ℂ] W} (hT : Function.Injective T) {E : Fin n → Fin n → Module.End ℂ V}
    {F : Fin n → Fin n → Module.End ℂ W} (h : ∀ a b y, T (E a b y) = F a b (T y)) (hF : GlRel F) : GlRel E := by
  intro a b c d
  refine LinearMap.ext fun y => hT ?_
  have key := LinearMap.congr_fun (hF a b c d) (T y)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, h, h, h, h, key]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, h]

theorem pair_of_inj {T : V →ₗ[ℂ] W} (hT : Function.Injective T) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {F1 F2 : Fin n → Fin n → Module.End ℂ W} (h : MorQ T E1 E2 F1 F2) (hF : PairRel F1 F2) : PairRel E1 E2 := by
  refine ⟨gl_of_inj hT h.h1 hF.1, gl_of_inj hT h.h2 hF.2.1, fun a b c d => ?_⟩
  show _ * _ = _ * _
  refine LinearMap.ext fun y => hT ?_
  have key := LinearMap.congr_fun (hF.2.2 a b c d).eq (T y)
  simp only [Module.End.mul_apply] at key ⊢
  rw [h.h1, h.h2, h.h2, h.h1, key]

def ShiftAt (n : ℕ) (lev : Fin n → ℕ) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (S : Lt n → Prop) (j : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ x : Cq n V, SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
      ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
        liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def HypAB (n : ℕ) (lev : Fin n → ℕ) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (S : Lt n → Prop) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
    ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

theorem shift_zero {lev : Fin n → ℕ} {a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} {S : Lt n → Prop}
    (hA : HypAB n lev a b S) : ShiftAt n lev a b S 0 := by
  intro V _ _ E1 E2 hE x _ hx _
  obtain ⟨w, hw⟩ := (hA V E1 E2 hE).2 (x ∅)
  let t : Cq n V := ∑ l : Lt n, if inUL lev l then Pi.single {l} (w l) else 0
  refine ⟨t, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem (supSub V _) fun l _ => ?_
    split_ifs with h
    · exact single_one_supp h _
    · exact Submodule.zero_mem (supSub V _)
  · refine Submodule.sum_mem (supSub V _) fun l _ => ?_
    split_ifs
    · exact single_one_deg l _
    · exact Submodule.zero_mem (supSub V _)
  · have e : bdq E1 E2 t = Pi.single ∅ (∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) := by
      have h1 : ∀ l : Lt n, bdq E1 E2 (if inUL lev l then (Pi.single {l} (w l) : Cq n V) else 0) =
          Pi.single ∅ (if inUL lev l then Tl E1 E2 l (w l) else 0) := by
        intro l
        split_ifs
        · exact bd_single E1 E2 l _
        · simp
      simp only [t, map_sum, h1]
      exact (map_sum (AddMonoidHom.single (fun _ : Finset (Lt n) => V) ∅) _ _).symm
    rw [e, ← hw, eq_single hx, lift_single, evC_single, ← Pi.single_sub]
    simp

theorem shift_step (hR : LeviRel) {lev : Fin n → ℕ} (hlev : Monotone lev) {a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {S : Lt n → Prop} (hS : IsSubL lev S) (hA : HypAB n lev a b S) {j : ℕ} (IH : ShiftAt n lev a b S j) :
    ShiftAt n lev a b S (j + 1) := by
  classical
  intro V _ _ E1 E2 hE x hxS hx hxb
  obtain ⟨Y, _, _, F1, F2, π, hF, hπ, h1, h2, hY⟩ := coverQ lev E1 E2 hE
  have hm : MorQ π F1 F2 E1 E2 := ⟨h1, h2⟩

  let x' : Cq n Y := fun A => if x A = 0 then 0 else Function.surjInv hπ (x A)
  have hx'π : liftq n π x' = x := by
    funext A
    by_cases h : x A = 0
    · simp [lift_apply, x', h]
    · simp [lift_apply, x', h, Function.surjInv_eq hπ]
  have hne : ∀ A, x' A ≠ 0 → x A ≠ 0 := by
    intro A hA0 h0
    exact hA0 (by simp [x', h0])
  have hx'D : DegQ (j + 1) x' := fun A h => hx A (hne A h)
  have hx'S : SuppQ S x' := fun A h => hxS A (hne A h)
  have hz0 : liftq n π (bdq F1 F2 x') = 0 := by rw [hm.bd, hx'π, hxb]

  have hk1 : ∀ a b, ∀ y ∈ LinearMap.ker π, F1 a b y ∈ LinearMap.ker π := by
    intro a b y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [h1, hy, map_zero]
  have hk2 : ∀ a b, ∀ y ∈ LinearMap.ker π, F2 a b y ∈ LinearMap.ker π := by
    intro a b y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [h2, hy, map_zero]
  let G1 : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (F1 a b).restrict (hk1 a b)
  let G2 : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (F2 a b).restrict (hk2 a b)
  have hι : MorQ (LinearMap.ker π).subtype G1 G2 F1 F2 := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  have hinj : Function.Injective (LinearMap.ker π).subtype := Submodule.injective_subtype _
  have hG : PairRel G1 G2 := pair_of_inj hinj hι hF

  let z' : Cq n (LinearMap.ker π) := fun A => ⟨bdq F1 F2 x' A, congrFun hz0 A⟩
  have hz' : liftq n (LinearMap.ker π).subtype z' = bdq F1 F2 x' := rfl
  have hne' : ∀ A, z' A ≠ 0 → bdq F1 F2 x' A ≠ 0 := by
    intro A hA0 h0
    exact hA0 (Subtype.ext h0)
  have hzD : DegQ j z' := fun A h => bd_deg F1 F2 hx'D A (hne' A h)
  have hzS : SuppQ S z' := fun A h => bd_supp F1 F2 (cq_closed hS) hx'S A (hne' A h)
  have hzc : bdq G1 G2 z' = 0 := by
    funext A
    apply hinj
    have e := congrFun (hι.bd z') A
    rw [hz'] at e
    have e2 : bdq F1 F2 (bdq F1 F2 x') = 0 := LinearMap.congr_fun (bdq_sq hF) x'
    rw [e2] at e
    simpa [lift_apply] using e
  obtain ⟨w', hw'S, hw'D, hw'⟩ := IH (LinearMap.ker π) G1 G2 hG z' hzS hzD hzc
  have e1 : liftq n (ev2 F1 F2 a) (bdq F1 F2 x') - evB lev (c1 F1 F2) (c2 F1 F2) b (bdq F1 F2 x') =
      bdq F1 F2 (liftq n (LinearMap.ker π).subtype w') := by
    have := congrArg (liftq n (LinearMap.ker π).subtype) hw'
    rwa [map_sub, hι.lift_ev, hι.evC lev, hι.bd, hz'] at this

  let u : Cq n Y := liftq n (ev2 F1 F2 a) x' - evB lev (c1 F1 F2) (c2 F1 F2) b x' - liftq n (LinearMap.ker π).subtype w'
  have hx'U : SuppQ (inUL lev) x' := fun A h l hl => hS.1 l (hx'S A h l hl)
  obtain ⟨f1, f2, f3⟩ := evC_facts hR hlev hF b x' hx'U
  have hub : bdq F1 F2 u = 0 := by
    have cc := lift_bd_comm (hA Y F1 F2 hF).1 hx'S
    simp only [u, map_sub]
    rw [← cc, f3, e1, sub_self]
  have huD : DegQ (j + 1) u := by
    have d1 : liftq n (ev2 F1 F2 a) x' ∈ supSub Y (fun A => A.card = j + 1) := lift_mem _ hx'D
    have d2 : evB lev (c1 F1 F2) (c2 F1 F2) b x' ∈ supSub Y (fun A => A.card = j + 1) := f2 _ hx'D
    have d3 : liftq n (LinearMap.ker π).subtype w' ∈ supSub Y (fun A => A.card = j + 1) := lift_mem _ hw'D
    exact Submodule.sub_mem _ (Submodule.sub_mem _ d1 d2) d3
  have huS : SuppQ (inUL lev) u := by
    have d1 : liftq n (ev2 F1 F2 a) x' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := lift_mem _ hx'U
    have d2 : evB lev (c1 F1 F2) (c2 F1 F2) b x' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := f1
    have d3 : liftq n (LinearMap.ker π).subtype w' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := lift_mem _ hw'S
    exact Submodule.sub_mem _ (Submodule.sub_mem _ d1 d2) d3
  obtain ⟨t, htS, htD, ht⟩ := hY j u huS huD hub
  refine ⟨liftq n π t, lift_mem π htS, lift_mem π htD, ?_⟩
  rw [← hm.bd, ht]
  have e0 : liftq n π (liftq n (LinearMap.ker π).subtype w') = 0 := by
    funext A
    exact (w' A).2
  simp only [u, map_sub, e0, sub_zero]
  rw [hm.lift_ev, hm.evC lev, hx'π]

theorem genCOU2_of (hR : LeviRel) : GenCOU2 := by
  intro n lev S a b hlev hS hA V _ _ E1 E2 hE j
  have key : ∀ j, ShiftAt n lev a b S j := by
    intro j
    induction j with
    | zero => exact shift_zero hA
    | succ j ih => exact shift_step hR hlev hS hA ih
  exact key j V E1 E2 hE

theorem genCOU2 : GenCOU2 := genCOU2_of GlobalTheory.CompanionTheory.PairMult.leviRel

end GlobalTheory.CompanionTheory.PairMult.COU
