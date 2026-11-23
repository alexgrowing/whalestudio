import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityGenericUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycleStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairBridge

open CompanionTheory.D.LK (Pos key)
open PositivityTheory.RgBcC.RealD (annL creL liftL xL bdL adLL adCL evLc evLv evKP kA pA inUU omU SuppL DegL IsPairA)
open GlobalTheory.CompanionTheory.PairMult (annq creq liftq Tl Ts bdq adLq lFq c1 c2 ev2 evB SuppQ DegQ inUL inKU omQ topq PairRel IsSubL)

variable {n : ℕ}

abbrev Lr (n : ℕ) : Type := Bool × Pos n

def fl : Lr n ≃ Lr n where
  toFun l := (!l.1, l.2)
  invFun l := (!l.1, l.2)
  left_inv l := by simp
  right_inv l := by simp

@[simp] theorem fl_fl (l : Lr n) : fl (fl l) = l := by simp [fl]

@[simp] theorem fl_fst (l : Lr n) : (fl l).1 = !l.1 := rfl

@[simp] theorem fl_snd (l : Lr n) : (fl l).2 = l.2 := rfl

def flS (A : Finset (Lr n)) : Finset (Lr n) := A.map fl.toEmbedding

theorem mem_flS {l : Lr n} {A : Finset (Lr n)} : l ∈ flS A ↔ fl l ∈ A := by
  unfold flS
  rw [Finset.mem_map_equiv]
  rfl

@[simp] theorem flS_flS (A : Finset (Lr n)) : flS (flS A) = A := by
  ext l
  simp [mem_flS]

theorem flS_insert (l : Lr n) (A : Finset (Lr n)) : flS (insert (fl l) A) = insert l (flS A) := by
  ext m
  simp [mem_flS, fl.injective.eq_iff]

theorem flS_erase (l : Lr n) (A : Finset (Lr n)) : flS (A.erase (fl l)) = (flS A).erase l := by
  ext m
  simp [mem_flS, fl.injective.eq_iff]

theorem card_flS (A : Finset (Lr n)) : (flS A).card = A.card := by simp [flS]

theorem key_lt (i : Pos n) : key i < n * n := by
  have h1 : (i.1.1 : ℕ) < i.1.2 := i.2
  have h2 : (i.1.2 : ℕ) < n := i.1.2.2
  have h3 : (i.1.1 : ℕ) + 1 ≤ n := by omega
  have h4 : ((i.1.1 : ℕ) + 1) * n ≤ n * n := Nat.mul_le_mul_right n h3
  unfold key
  nlinarith

theorem key_iff (m l : Lr n) : PositivityTheory.RgBcC.RealD.keyL m < PositivityTheory.RgBcC.RealD.keyL l ↔
    GlobalTheory.CompanionTheory.PairMult.keyL (fl m) < GlobalTheory.CompanionTheory.PairMult.keyL (fl l) := by
  obtain ⟨s, i⟩ := m
  obtain ⟨t, j⟩ := l
  have hi := key_lt i
  have hj := key_lt j
  have hn : n * n ≤ (n + 1) * (n + 1) := by nlinarith
  cases s <;> cases t <;> simp [PositivityTheory.RgBcC.RealD.keyL, GlobalTheory.CompanionTheory.PairMult.keyL, fl] <;> omega

theorem sg_eq (l : Lr n) (A : Finset (Lr n)) :
    PositivityTheory.RgBcC.RealD.sgL l (flS A) = GlobalTheory.CompanionTheory.PairMult.sgL (fl l) A := by
  unfold PositivityTheory.RgBcC.RealD.sgL GlobalTheory.CompanionTheory.PairMult.sgL
  congr 1
  unfold flS
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  have := key_iff (fl j) l
  simpa using this

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def Phi : (Finset (Lr n) → V) →ₗ[ℂ] (Finset (Lr n) → V) := LinearMap.funLeft ℂ V flS

theorem Phi_apply (x : Finset (Lr n) → V) (A : Finset (Lr n)) : Phi x A = x (flS A) := rfl

@[simp] theorem Phi_Phi (x : Finset (Lr n) → V) : Phi (Phi x) = x := by
  funext A
  simp [Phi_apply]

theorem Phi_ann (l : Lr n) (x : Finset (Lr n) → V) : Phi (annL l x) = annq (fl l) (Phi x) := by
  funext A
  show (if l ∈ flS A then 0 else PositivityTheory.RgBcC.RealD.sgL l (flS A) • x (insert l (flS A))) =
    if fl l ∈ A then 0 else GlobalTheory.CompanionTheory.PairMult.sgL (fl l) A • x (flS (insert (fl l) A))
  simp only [mem_flS, sg_eq, flS_insert]

theorem Phi_cre (l : Lr n) (x : Finset (Lr n) → V) : Phi (creL l x) = creq (fl l) (Phi x) := by
  funext A
  show (if l ∈ flS A then PositivityTheory.RgBcC.RealD.sgL l (flS A) • x ((flS A).erase l) else 0) =
    if fl l ∈ A then GlobalTheory.CompanionTheory.PairMult.sgL (fl l) A • x (flS (A.erase (fl l))) else 0
  simp only [mem_flS, sg_eq, flS_erase]

theorem Phi_lift (T : V →ₗ[ℂ] V) (x : Finset (Lr n) → V) : Phi (liftL n T x) = liftq n T (Phi x) := rfl

theorem xL_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lr n) : xL E1 E2 l = Tl E1 E2 (fl l) := by
  obtain ⟨s, i⟩ := l
  cases s <;> simp [xL, Tl, Ts, fl, kA, pA]

def supS (V : Type) [AddCommGroup V] [Module ℂ V] (P : Lr n → Prop) : Submodule ℂ (Finset (Lr n) → V) where
  carrier := {x | SuppL P x}
  add_mem' := by
    intro x y hx hy A h l hl
    by_contra hP
    have h1 : x A = 0 := by_contra fun h0 => hP (hx A h0 l hl)
    have h2 : y A = 0 := by_contra fun h0 => hP (hy A h0 l hl)
    exact h (by simp [h1, h2])
  zero_mem' := fun A h => absurd rfl h
  smul_mem' := by
    intro c x hx A h l hl
    by_contra hP
    have h1 : x A = 0 := by_contra fun h0 => hP (hx A h0 l hl)
    exact h (by simp [h1])

theorem mem_supS {P : Lr n → Prop} {x : Finset (Lr n) → V} : x ∈ supS V P ↔ SuppL P x := Iff.rfl

theorem ann_zero {P : Lr n → Prop} {x : Finset (Lr n) → V} (hx : SuppL P x) {l : Lr n} (hl : ¬ P l) :
    annL l x = 0 := by
  funext A
  show (if l ∈ A then 0 else PositivityTheory.RgBcC.RealD.sgL l A • x (insert l A)) = 0
  by_cases h : l ∈ A
  · simp [h]
  · have : x (insert l A) = 0 := by_contra fun h0 => hl (hx _ h0 l (Finset.mem_insert_self l A))
    simp [h, this]

theorem ann_supp {P : Lr n → Prop} {x : Finset (Lr n) → V} (hx : SuppL P x) (l : Lr n) : SuppL P (annL l x) := by
  intro A hA m hm
  have h1 : (if l ∈ A then 0 else PositivityTheory.RgBcC.RealD.sgL l A • x (insert l A)) ≠ 0 := hA
  by_cases h : l ∈ A
  · simp [h] at h1
  · rw [if_neg h] at h1
    have h2 : x (insert l A) ≠ 0 := fun h0 => h1 (by rw [h0, smul_zero])
    exact hx _ h2 m (Finset.mem_insert_of_mem hm)

theorem cre_supp {P : Lr n → Prop} {x : Finset (Lr n) → V} (hx : SuppL P x) {l : Lr n} (hl : P l) :
    SuppL P (creL l x) := by
  intro A hA m hm
  have h1 : (if l ∈ A then PositivityTheory.RgBcC.RealD.sgL l A • x (A.erase l) else 0) ≠ 0 := hA
  by_cases h : l ∈ A
  · rw [if_pos h] at h1
    have h2 : x (A.erase l) ≠ 0 := fun h0 => h1 (by rw [h0, smul_zero])
    by_cases hml : m = l
    · exact hml ▸ hl
    · exact hx _ h2 m (Finset.mem_erase.2 ⟨hml, hm⟩)
  · simp [h] at h1

open Classical in
theorem bdL_apply (S : Lr n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Finset (Lr n) → V) :
    bdL S E1 E2 x = (∑ l : Lr n, if S l then liftL n (xL E1 E2 l) (annL l x) else 0) +
      ∑ l : Lr n, ∑ m : Lr n, ∑ k : Lr n,
        if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          creL k (annL m (annL l x)) else 0 := by
  unfold bdL
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [Module.End.mul_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp [Module.End.mul_apply]

theorem bdq_apply (E1 E2 : Fin n → Fin n → Module.End ℂ V) (y : Finset (Lr n) → V) :
    bdq E1 E2 y = (∑ l : Lr n, liftq n (Tl E1 E2 l) (annq l y)) +
      ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) (annq (t, j) (annq (s, i) y)) else 0 := by
  unfold bdq
  rw [LinearMap.add_apply]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [LinearMap.sum_apply]
    rfl
  · rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rfl
    · rfl

theorem sum_letters {M : Type} [AddCommGroup M] (H : Lr n → Lr n → Lr n → M) :
    (∑ l : Lr n, ∑ m : Lr n, ∑ k : Lr n,
      if l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then H (fl l) (fl m) (fl k) else 0) =
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then H (s, i) (t, j) ((s == t), k) else 0 := by
  have e : ∀ l m : Lr n, (∑ k : Lr n,
      if (fl l).2.1.2 = (fl m).2.1.1 ∧ k.1 = xor (fl l).1 (fl m).1 ∧ k.2.1.1 = (fl l).2.1.1 ∧ k.2.1.2 = (fl m).2.1.2 then
        H (fl (fl l)) (fl (fl m)) (fl k) else 0) =
      ∑ k : Pos n, if l.2.1.2 = m.2.1.1 ∧ k.1.1 = l.2.1.1 ∧ k.1.2 = m.2.1.2 then H l m ((l.1 == m.1), k) else 0 := by
    intro l m
    rw [← Equiv.sum_comp fl, Fintype.sum_prod_type, Fintype.sum_bool]
    obtain ⟨s, i⟩ := l
    obtain ⟨t, j⟩ := m
    cases s <;> cases t <;> simp [fl]
  rw [← Equiv.sum_comp fl]
  have e2 : ∀ l : Lr n, (∑ m : Lr n, ∑ k : Lr n,
      if (fl l).2.1.2 = m.2.1.1 ∧ k.1 = xor (fl l).1 m.1 ∧ k.2.1.1 = (fl l).2.1.1 ∧ k.2.1.2 = m.2.1.2 then
        H (fl (fl l)) (fl m) (fl k) else 0) =
      ∑ t : Bool, ∑ j : Pos n, ∑ k : Pos n,
        if l.2.1.2 = j.1.1 ∧ k.1.1 = l.2.1.1 ∧ k.1.2 = j.1.2 then H l (t, j) ((l.1 == t), k) else 0 := by
    intro l
    rw [← Equiv.sum_comp fl]
    refine (Finset.sum_congr rfl fun m _ => e l m).trans ?_
    rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun l _ => e2 l).trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact Finset.sum_comm

open Classical in
theorem Phi_bd (S : Lr n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {x : Finset (Lr n) → V} (hx : SuppL S x) :
    Phi (bdL S E1 E2 x) = bdq E1 E2 (Phi x) := by
  rw [bdL_apply, bdq_apply, map_add, map_sum, map_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← Equiv.sum_comp fl (fun l => liftq n (Tl E1 E2 l) (annq l (Phi x)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : S l
    · rw [if_pos h, Phi_lift, Phi_ann, xL_eq]
    · rw [if_neg h, map_zero, ← Phi_ann, ann_zero hx h, map_zero, map_zero]
  · rw [← sum_letters (fun l m k => creq k (annq m (annq l (Phi x))))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : Phi (creL k (annL m (annL l x))) = creq (fl k) (annq (fl m) (annq (fl l) (Phi x))) := by
      rw [Phi_cre, Phi_ann, Phi_ann]
    by_cases hR : l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2
    · rw [if_pos hR]
      by_cases hl : S l
      · by_cases hm : S m
        · rw [if_pos ⟨hl, hm, hR⟩, hk]
        · rw [if_neg (fun h => hm h.2.1), map_zero, ← hk, ann_zero (ann_supp hx l) hm]
          simp
      · rw [if_neg (fun h => hl h.1), map_zero, ← hk, ann_zero hx hl]
        simp
    · rw [if_neg hR, if_neg (fun h => hR h.2.2), map_zero]

theorem adLL_apply (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) (x : Finset (Lr n) → V) :
    adLL lev s p q x = ∑ l : Lr n, ∑ k : Lr n,
      if inUU lev l then adCL s p q l k • creL k (annL l x) else 0 := by
  unfold adLL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · rfl

theorem adLq_apply (s : Bool) (p q : Fin n) (y : Finset (Lr n) → V) :
    adLq s p q y = ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n,
      CompanionTheory.RgExh.U.adC p q i k • creq ((s == t), k) (annq (t, i) y) := by
  unfold adLq
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem adC_eq (s t c : Bool) (p q : Fin n) (i k : Pos n) :
    adCL s p q (fl (t, i)) (fl (c, k)) = if c = (!s == t) then CompanionTheory.RgExh.U.adC p q i k else 0 := by
  cases s <;> cases t <;> cases c <;> simp [adCL, fl, CompanionTheory.RgExh.U.adC]

theorem Phi_ad (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) {x : Finset (Lr n) → V} (hx : SuppL (inUU lev) x) :
    Phi (adLL lev s p q x) = adLq (!s) p q (Phi x) := by
  rw [adLL_apply, adLq_apply, map_sum]
  have h1 : ∀ l k : Lr n, Phi (if inUU lev l then adCL s p q l k • creL k (annL l x) else 0) =
      adCL s p q l k • creq (fl k) (annq (fl l) (Phi x)) := by
    intro l k
    by_cases h : inUU lev l
    · rw [if_pos h, map_smul, Phi_cre, Phi_ann]
    · rw [if_neg h, map_zero, ← Phi_ann, ann_zero hx h]
      simp
  have h2 : ∀ l : Lr n, Phi (∑ k : Lr n, if inUU lev l then adCL s p q l k • creL k (annL l x) else 0) =
      ∑ k : Lr n, adCL s p q l k • creq (fl k) (annq (fl l) (Phi x)) := by
    intro l
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => h1 l k
  refine (Finset.sum_congr rfl fun l _ => h2 l).trans ?_
  rw [← Equiv.sum_comp fl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp fl, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [adC_eq, fl_fl]
  cases s <;> cases t <;> simp

def tau : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if p.1 then FreeAlgebra.ι ℂ (true, p.2) - FreeAlgebra.ι ℂ (false, p.2)
    else FreeAlgebra.ι ℂ (true, p.2) + FreeAlgebra.ι ℂ (false, p.2)

theorem evalPair_tau_eq_evalKPair (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ev2 E1 E2 (tau a) = evKP E1 E2 a := by
  have h : (ev2 E1 E2).comp tau = evKP E1 E2 := by
    refine FreeAlgebra.hom_ext ?_
    funext p
    obtain ⟨s, p, q⟩ := p
    cases s <;> simp [tau, ev2, evKP, pA, kA]
  exact DFunLike.congr_fun h a

theorem evB_tau (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    evB lev E1 E2 (tau b) = evLv lev E1 E2 b := by
  have h : (evB lev E1 E2).comp tau = evLv lev E1 E2 := by
    refine FreeAlgebra.hom_ext ?_
    funext p
    obtain ⟨s, p, q⟩ := p
    by_cases hl : lev p = lev q <;> cases s <;> simp [tau, evB, evLv, pA, kA, hl]
  exact DFunLike.congr_fun h b

theorem c_add (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    c1 E1 E2 p q + c2 E1 E2 p q = lFq E1 E2 true p q := by
  unfold c1 c2
  rw [← smul_add]
  have : lFq E1 E2 true p q + lFq E1 E2 false p q + (lFq E1 E2 true p q - lFq E1 E2 false p q) =
      (2 : ℂ) • lFq E1 E2 true p q := by
    rw [two_smul]
    abel
  rw [this, smul_smul]
  norm_num

theorem c_sub (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    c1 E1 E2 p q - c2 E1 E2 p q = lFq E1 E2 false p q := by
  unfold c1 c2
  rw [← smul_sub]
  have : lFq E1 E2 true p q + lFq E1 E2 false p q - (lFq E1 E2 true p q - lFq E1 E2 false p q) =
      (2 : ℂ) • lFq E1 E2 false p q := by
    rw [two_smul]
    abel
  rw [this, smul_smul]
  norm_num

theorem lift_supp {P : Lr n → Prop} {x : Finset (Lr n) → V} (hx : SuppL P x) (T : V →ₗ[ℂ] V) :
    SuppL P (liftL n T x) := by
  intro A hA
  refine hx A fun h => hA ?_
  show T (x A) = 0
  rw [h, map_zero]

theorem ad_supp (lev : Fin n → ℕ) (s : Bool) {p q : Fin n} (hpq : lev p = lev q) {x : Finset (Lr n) → V}
    (hx : SuppL (inUU lev) x) : SuppL (inUU lev) (adLL lev s p q x) := by
  rw [adLL_apply, ← mem_supS]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun k _ => ?_
  by_cases hl : inUU lev l
  · rw [if_pos hl]
    by_cases hc : adCL s p q l k = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ ?_
      have hk : inUU lev k := by
        by_contra hk
        apply hc
        have h0 : lev l.2.1.1 < lev l.2.1.2 := hl
        have h1 : ¬ (q = l.2.1.1 ∧ k.1 = xor s l.1 ∧ k.2.1 = (p, l.2.1.2)) := by
          rintro ⟨rfl, _, h3⟩
          apply hk
          show lev k.2.1.1 < lev k.2.1.2
          rw [h3]
          simpa [hpq] using h0
        have h2 : ¬ (l.2.1.2 = p ∧ k.1 = xor s l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
          rintro ⟨rfl, _, h3⟩
          apply hk
          show lev k.2.1.1 < lev k.2.1.2
          rw [h3]
          simpa [← hpq] using h0
        simp [adCL, h1, h2]
      exact cre_supp (ann_supp hx l) hk
  · rw [if_neg hl]
    exact Submodule.zero_mem _

theorem Phi_evLc (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ x : Finset (Lr n) → V, SuppL (inUU lev) x → SuppL (inUU lev) (evLc lev E1 E2 b x) ∧
      Phi (evLc lev E1 E2 b x) = evB lev (c1 E1 E2) (c2 E1 E2) (tau b) (Phi x) := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    intro x hx
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact ⟨(supS V (inUU lev)).smul_mem r hx, map_smul Phi r x⟩
  | grade1 p =>
    intro x hx
    obtain ⟨s, p, q⟩ := p
    by_cases hl : lev p = lev q
    · have e1 : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p, q)) x =
          liftL n (if s then pA E1 E2 p q else kA E1 E2 p q) x + adLL lev s p q x := by
        simp [evLc, hl]
      have e2 : evB lev (c1 E1 E2) (c2 E1 E2) (tau (FreeAlgebra.ι ℂ (s, p, q))) = lFq E1 E2 (!s) p q := by
        cases s <;> simp [tau, evB, hl, c_add, c_sub]
      rw [e1, e2]
      refine ⟨(supS V (inUU lev)).add_mem (lift_supp hx _) (ad_supp lev s hl hx), ?_⟩
      rw [map_add, Phi_lift, Phi_ad lev s p q hx]
      have e3 : lFq E1 E2 (!s) p q (Phi x) = liftq n (Ts E1 E2 (!s) p q) (Phi x) + adLq (!s) p q (Phi x) := by
        unfold lFq
        rw [LinearMap.add_apply]
      rw [e3]
      cases s <;> simp [Ts, kA, pA]
    · have e1 : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p, q)) = 0 := by simp [evLc, hl]
      have e2 : evB lev (c1 E1 E2) (c2 E1 E2) (tau (FreeAlgebra.ι ℂ (s, p, q))) = 0 := by
        cases s <;> simp [tau, evB, hl]
      rw [e1, e2]
      simp only [LinearMap.zero_apply, map_zero]
      exact ⟨(supS V (inUU lev)).zero_mem, trivial⟩
  | mul a b ha hb =>
    intro x hx
    obtain ⟨h1, h2⟩ := hb x hx
    obtain ⟨h3, h4⟩ := ha _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h3, by rw [h4, h2]⟩
  | add a b ha hb =>
    intro x hx
    obtain ⟨h1, h2⟩ := ha x hx
    obtain ⟨h3, h4⟩ := hb x hx
    simp only [map_add, LinearMap.add_apply]
    exact ⟨(supS V (inUU lev)).add_mem h1 h3, by rw [h2, h4]⟩

theorem flS_omQ (lev : Fin n → ℕ) : flS (omQ lev) = omU lev := by
  ext l
  obtain ⟨s, i⟩ := l
  cases s <;> simp [mem_flS, omQ, omU, fl]

theorem Phi_top (lev : Fin n → ℕ) (u : V) : Phi (Pi.single (omU lev) u) = topq lev u := by
  funext A
  rw [Phi_apply]
  unfold topq
  by_cases h : A = omQ lev
  · subst h
    rw [flS_omQ]
    simp
  · have h' : flS A ≠ omU lev := by
      intro h2
      apply h
      rw [← flS_omQ] at h2
      have := congrArg flS h2
      simpa using this
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

theorem lift_top (lev : Fin n → ℕ) (T : V →ₗ[ℂ] V) (u : V) : liftq n T (topq lev u) = topq lev (T u) := by
  funext A
  show T (topq lev u A) = topq lev (T u) A
  unfold topq
  by_cases h : A = omQ lev
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem single_supp (lev : Fin n → ℕ) (u : V) : SuppL (inUU lev) (Pi.single (omU lev) u : Finset (Lr n) → V) := by
  intro A hA l hl
  have hAe : A = omU lev := by
    by_contra h
    exact hA (Pi.single_eq_of_ne h _)
  subst hAe
  exact (Finset.mem_filter.1 hl).2.2

theorem top_supp (lev : Fin n → ℕ) (u : V) : SuppQ (inKU lev) (topq lev u) := by
  intro A hA l hl
  have hAe : A = omQ lev := by
    by_contra h
    exact hA (Pi.single_eq_of_ne h _)
  subst hAe
  exact (Finset.mem_filter.1 hl).2

theorem top_deg (lev : Fin n → ℕ) (u : V) : DegQ (omQ lev).card (topq lev u) := by
  intro A hA
  have hAe : A = omQ lev := by
    by_contra h
    exact hA (Pi.single_eq_of_ne h _)
  rw [hAe]

end Chains

theorem isSubL_inKU (lev : Fin n → ℕ) : IsSubL lev (inKU lev) := by
  refine ⟨fun l h => h.2, ?_⟩
  intro s t i j k h1 h2 h3 hs ht
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  simp only at hs1 ht1 hs2 ht2
  subst hs1 ht1
  refine ⟨rfl, ?_⟩
  show lev k.1.1 < lev k.1.2
  rw [h2, h3]
  rw [h1] at hs2
  exact hs2.trans ht2

theorem omQ_card (lev : Fin n → ℕ) : (omQ lev).card = (omU lev).card := by
  rw [← flS_omQ, card_flS]

theorem actUU_of (hG : GlobalTheory.CompanionTheory.PairMult.GenCOU2) (hT : GlobalTheory.CompanionTheory.PairMult.TopCyc) : PositivityTheory.RgBcC.RealD.ActUU := by
  intro n lev hlev a b ha hab V _ _ E1 E2 hE v hv
  have hP : PairRel E1 E2 := hE
  have hcyc : bdq E1 E2 (topq lev v) = 0 := by
    refine hT n lev V E1 E2 hP v ?_
    rintro ⟨s, i⟩ ⟨hs, hi⟩
    simp only at hs
    subst hs
    have := hv (fl (true, i)) rfl hi
    rwa [xL_eq, fl_fl] at this
  obtain ⟨w, hw1, hw2, hw3⟩ := hG n lev (inKU lev) (tau a) (tau b) hlev (isSubL_inKU lev) (by
    intro V _ _ E1 E2 hP
    refine ⟨?_, ?_⟩
    · rintro ⟨s, i⟩ ⟨hs, _⟩
      simp only at hs
      subst hs
      rw [evalPair_tau_eq_evalKPair]
      exact ha V E1 E2 hP i.1.1 i.1.2
    · intro x
      obtain ⟨w, hw⟩ := hab V E1 E2 hP x
      refine ⟨fun l => w (fl l), ?_⟩
      rw [evalPair_tau_eq_evalKPair, evB_tau, hw, ← Equiv.sum_comp fl]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : inUU lev l
      · rw [if_pos h, if_pos (show inUL lev (fl l) from h), xL_eq, fl_fl]
      · rw [if_neg h, if_neg (show ¬ inUL lev (fl l) from h)]) V E1 E2 hP (omQ lev).card (topq lev v)
    (top_supp lev v) (top_deg lev v) hcyc
  have hsw : SuppL (inUU lev) (Phi w) := by
    intro A hA l hl
    exact hw1 (flS A) hA (fl l) (by simpa [mem_flS] using hl)
  have hdw : DegL ((omU lev).card + 1) (Phi w) := by
    intro A hA
    rw [← omQ_card, ← hw2 (flS A) hA, card_flS]
  refine ⟨Phi w, hsw, hdw, ?_⟩
  apply (show Function.Injective (Phi : (Finset (Lr n) → V) → _) from
    Function.LeftInverse.injective Phi_Phi)
  rw [Phi_bd _ E1 E2 hsw, Phi_Phi, ← hw3, map_sub, Phi_top, (Phi_evLc lev E1 E2 b _ (single_supp lev v)).2, Phi_top,
    lift_top, evalPair_tau_eq_evalKPair]

theorem actUU : PositivityTheory.RgBcC.RealD.ActUU := actUU_of GlobalTheory.T.pair_multiplicity_generic_unitary GlobalTheory.T.pair_multiplicity_top_cycle

end GlobalTheory.CompanionTheory.PairBridge
