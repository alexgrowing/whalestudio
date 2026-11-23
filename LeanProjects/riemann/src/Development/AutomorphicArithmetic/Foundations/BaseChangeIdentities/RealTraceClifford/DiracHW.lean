import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracAlg
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnCas
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Gelf2

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  have h1 : (univ.filter fun b : Fin n => a < b ∧ True) = Finset.Ioi a := by
    ext b; simp
  have h2 : (univ.filter fun b : Fin n => b < a ∧ True) = Finset.Iio a := by
    ext b; simp
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have := a.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [Formalism.REAL.rhoC, rhoV, eq_self_iff_true]
  rw [h1, h2, Fin.card_Ioi, Fin.card_Iio, h3]
  ring

private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

private theorem cas_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (F : Fin n → Fin n → A) : φ (Cas F) = Cas fun a b => φ (F a b) := by
  simp [Cas, map_sum, map_mul]

private theorem spn_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (c : Fin n → Fin n → A) (a b : Fin n) : φ (spn c a b) = spn (fun a b => φ (c a b)) a b := by
  by_cases h : a = b <;> simp [spn, map_sum, map_sub, map_mul, h]

private theorem gl_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {F : Fin n → Fin n → A} (h : GlRel F) : GlRel fun a b => φ (F a b) := by
  intro a b c d
  have := congrArg φ (h a b c d)
  simp only [map_sub, map_mul] at this
  rw [this]
  split_ifs <;> simp

private theorem clif_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {c : Fin n → Fin n → A} (h : Clif c) : Clif fun a b => φ (c a b) := by
  intro a b d e
  have := congrArg φ (h a b d e)
  simp only [map_add, map_mul] at this
  rw [this]
  split_ifs <;> simp

private theorem cas_gel {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA E 2 := by
  simp [Cas, gelA, epow, Finset.sum_ite_eq]

private theorem cas_bar {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA (barF E) 2 := by
  rw [← cas_gel, Cas, Cas, Finset.sum_comm]
  simp [barF]

private theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : GlRel (kF E1 E2) := by
  intro a b c d
  have e1 := hP.gl1 a b c d
  have e2 := hP.gl2 a b c d
  have h : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add]
    rw [hP.comm a b c d, hP.comm c d a b]
    abel
  simp only [kF]
  rw [h, e1, e2]
  split_ifs <;> abel

private theorem gel_val {n : ℕ} (lam : Fin n → ℤ) (s : Bool) :
    GlobalTheory.Dec.gelfVal (infOf lam s) 2 =
      (((nsq fun a => (lam a : ℝ) + rhoV n a) - nsq (rhoV n) : ℝ) : ℂ) := by
  rw [gelf2]
  have : ∀ a, infOf lam s a ^ 2 = ((((lam a : ℝ) + rhoV n a) ^ 2 : ℝ) : ℂ) := by
    intro a
    cases s <;> simp [infOf, rhoV] <;> ring
  simp only [this, nsq]
  push_cast
  rfl

private theorem lsq_eq {n : ℕ} (lam : Fin n → ℤ) :
    LSq lam = 4 * nsq fun a => (lam a : ℝ) + rhoV n a := by
  simp only [LSq, nsq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem UpperTheory.RealTr.diracHW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ κ : Wt n, hw (dg (kF E1 E2) c) κ ≠ ⊥ → LSq lam ≤ nsq (κ + rhoV n) := by
  intro n lam V _ _ E1 E2 hP _ h1 h2 J _ _ c η hC κ hκ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hκ
  have hx' : KHighest (fun _ => true) (dg (kF E1 E2) c) κ x := hx
  obtain ⟨⟨φ, hφ⟩, hcomm, hmadj, hladj, hUF⟩ := tenF n V J
  have hUFd : UF (dg (kF E1 E2) c) := hUF _ c η ⟨kF_gl hP, hP.unitK⟩ hC
  let lfJ : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Ten J V) := lf J
  let L1 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E1 a b)
  let L2 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E2 a b)
  let C : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => φ (c a b)
  have hD := diracAlg n (Module.End ℂ (Ten J V)) L1 L2 C (gl_map lfJ hP.gl1) (gl_map lfJ hP.gl2)
    (fun a b d e => by
      simp only [L1, L2, ← map_mul]
      rw [hP.comm a b d e])
    (clif_map φ hC.rel)
    (fun a b d e => by
      simp only [L1, L2, C, hφ]
      exact ⟨hcomm _ _, hcomm _ _⟩)
  set T : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => (L1 a b - L2 a b) * C b a with hTdef
  set D : Module.End ℂ (Ten J V) := ∑ a, ∑ b, T a b with hDdef
  have hT : ∀ a b (y z : Ten J V), ⟪T a b y, z⟫_ℂ = -⟪y, T b a z⟫_ℂ := by
    intro a b y z
    have hP' : L1 a b - L2 a b = lfJ (pF E1 E2 a b) := by simp [L1, L2, pF, map_sub]
    have hP'' : L1 b a - L2 b a = lfJ (pF E1 E2 b a) := by simp [L1, L2, pF, map_sub]
    have hneg : ∀ u w : V, ⟪pF E1 E2 a b u, w⟫_ℂ = ⟪u, (-(pF E1 E2 b a)) w⟫_ℂ := by
      intro u w
      rw [hP.unitP a b u w]
      simp [inner_neg_right]
    simp only [hTdef, hP', hP'', Module.End.mul_apply, C, hφ]
    rw [hladj _ _ hneg, hmadj, hC.adj b a, map_neg]
    have hc := LinearMap.congr_fun (hcomm (c a b) (pF E1 E2 b a)) z
    simp only [Module.End.mul_apply] at hc
    rw [LinearMap.neg_apply, map_neg, inner_neg_right]
    exact congrArg (fun w => -⟪y, w⟫_ℂ) hc.symm
  have hskew : ∀ y z : Ten J V, ⟪D y, z⟫_ℂ = -⟪y, D z⟫_ℂ := by
    intro y z
    calc ⟪D y, z⟫_ℂ = ∑ a, ∑ b, ⟪T a b y, z⟫_ℂ := by
          simp [hDdef, LinearMap.sum_apply, sum_inner]
      _ = ∑ a, ∑ b, -⟪y, T b a z⟫_ℂ := by simp_rw [hT]
      _ = -⟪y, D z⟫_ℂ := by
          rw [Finset.sum_comm]
          simp [hDdef, LinearMap.sum_apply, inner_sum, Finset.sum_neg_distrib]
  set A0 : ℝ := nsq fun a => (lam a : ℝ) + rhoV n a with hA0
  set R : ℝ := nsq (rhoV n) with hR
  set N : ℝ := nsq (κ + rhoV n) with hN
  have g1 : GlobalTheory.Dec.gelfVal (infOf lam true) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam true
  have g2 : GlobalTheory.Dec.gelfVal (infOf lam false) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam false
  have hc1 : Cas L1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_gel, h1 2 v, g1]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hc2 : Cas L2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_bar, h2 2 v, g2]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hspn : (fun a b => spn C a b) = fun a b => φ (spn c a b) := by
    funext a b
    exact (spn_map φ c a b).symm
  have hc3 : Cas (spn C) = ((3 * R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have e : Cas (spn C) = φ (Cas (spn c)) := by
      rw [cas_map φ]
      exact congrArg Cas hspn
    rw [e, spnCas n J c η hC, map_smul, map_one]
  have hdg : (fun a b => L1 a b + L2 a b + spn C a b) = dg (kF E1 E2) c := by
    funext a b
    have : spn C a b = mt V (spn c a b) := by rw [← hφ]; exact congrFun (congrFun hspn a) b
    simp only [dg, kF, L1, L2, lfJ, map_add, this]
  have hc4 : Cas (dg (kF E1 E2) c) x = ((N - R : ℝ) : ℂ) • x := by
    have h := Formalism.REAL.kCasSpan (Ten J V) n (fun _ => true) (dg (kF E1 E2) c) κ x
      (Formalism.REAL.glRel_kRel _ _ hUFd.gl) hx' x
      (Submodule.mem_sInf.2 fun S hS => hS.1)
    have hk : Formalism.REAL.CasK (fun _ : Fin n => true) (dg (kF E1 E2) c) = Cas (dg (kF E1 E2) c) := by
      simp [Formalism.REAL.CasK, Cas]
    rw [hk] at h
    rw [h, Formalism.REAL.ckv, rhoC_true, nsq_eq, nsq_eq]
  have key : D (D x) + D (D x) = ((LSq lam - N : ℝ) : ℂ) • x := by
    rw [hdg, hc1, hc2, hc3, two_mul, two_mul] at hD
    have h := LinearMap.congr_fun hD x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hc4] at h
    have h' : D (D x) + D (D x) = _ := h
    rw [h', lsq_eq, ← sub_eq_zero]
    simp only [← add_smul, ← sub_smul]
    rw [← hA0]
    convert zero_smul ℂ x using 2
    push_cast
    ring
  have e : ⟪x, D (D x)⟫_ℂ = -(((‖D x‖ ^ 2 : ℝ)) : ℂ) := by
    have h := hskew x (D x)
    rw [inner_self_eq_norm_sq_to_K] at h
    rw [eq_neg_iff_add_eq_zero] at h ⊢
    rw [← h]
    push_cast
    simp
    ring
  have h3 := congrArg (fun w => ⟪x, w⟫_ℂ) key
  simp only [inner_add_right, inner_smul_right, e, inner_self_eq_norm_sq_to_K] at h3
  have h4 : -(2 * ‖D x‖ ^ 2) = (LSq lam - N) * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    push_cast at h3
    linear_combination h3
  have hx2 : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx0
    positivity
  by_contra hlt
  have : 0 < LSq lam - N := sub_pos.2 (not_le.1 hlt)
  have := mul_pos this hx2
  nlinarith [sq_nonneg ‖D x‖]
