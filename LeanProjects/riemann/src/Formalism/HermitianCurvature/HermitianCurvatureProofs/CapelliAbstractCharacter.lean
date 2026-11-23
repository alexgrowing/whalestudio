import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation

open Finset Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

def IsPol {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) (f : ℂ → X) : Prop :=
  ∃ c : ℕ → X, ∀ u : ℂ, f u = ∑ s ∈ Finset.range d, (u ^ s) • c s

def shiftC {X : Type} [Zero X] (c : ℕ → X) : ℕ → X
  | 0 => 0
  | s + 1 => c s

section pol

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem IsPol.const (x : X) : IsPol 1 (fun _ => x) := by
  exact ⟨fun _ => x, fun u => by simp⟩

theorem IsPol.add {d : ℕ} {f g : ℂ → X} (hf : IsPol d f) (hg : IsPol d g) : IsPol d (fun u => f u + g u) := by
  obtain ⟨c1, h1⟩ := hf
  obtain ⟨c2, h2⟩ := hg
  exact ⟨fun s => c1 s + c2 s, fun u => by simp only [h1 u, h2 u, smul_add, Finset.sum_add_distrib]⟩

theorem IsPol.zero (d : ℕ) : IsPol d (fun _ => (0 : X)) := by
  exact ⟨fun _ => 0, fun u => by simp⟩

theorem IsPol.sum {ι : Type} (S : Finset ι) {d : ℕ} {f : ι → ℂ → X} (hf : ∀ i ∈ S, IsPol d (f i)) :
    IsPol d (fun u => ∑ i ∈ S, f i u) := by
  obtain ⟨c, hc⟩ := Finset.sum_induction f (IsPol d) (fun a b ha hb => IsPol.add ha hb) (IsPol.zero d) hf
  refine ⟨c, fun u => ?_⟩
  show ∑ i ∈ S, f i u = _
  rw [← Finset.sum_apply]
  exact hc u

theorem IsPol.map {d : ℕ} {f : ℂ → X} (L : X →ₗ[ℂ] Y) (hf : IsPol d f) : IsPol d (fun u => L (f u)) := by
  obtain ⟨c, h⟩ := hf
  exact ⟨fun s => L (c s), fun u => by simp only [h u, map_sum, map_smul]⟩

theorem IsPol.up {d : ℕ} {f : ℂ → X} (hf : IsPol d f) : IsPol (d + 1) f := by
  obtain ⟨c, h⟩ := hf
  refine ⟨fun s => if s < d then c s else 0, fun u => ?_⟩
  rw [Finset.sum_range_succ, h u]
  simp only [lt_irrefl, if_false, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s hs => by rw [if_pos (Finset.mem_range.mp hs)])

theorem IsPol.shift {d : ℕ} {f : ℂ → X} (hf : IsPol d f) : IsPol (d + 1) (fun u => u • f u) := by
  obtain ⟨c, h⟩ := hf
  refine ⟨shiftC c, fun u => ?_⟩
  show u • f u = _
  rw [Finset.sum_range_succ', h u, Finset.smul_sum]
  simp only [shiftC, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s _ => by rw [pow_succ', mul_smul])

end pol

theorem prod_isPol {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (α β : Fin t → A) :
    IsPol (t + 1) (fun u : ℂ => (List.ofFn fun k : Fin t => u • α k + β k).prod) := by
  induction t with
  | zero => simpa using IsPol.const (1 : A)
  | succ t ih =>
    have h1 := ih (fun k => α k.succ) (fun k => β k.succ)
    have h2 := (h1.map (LinearMap.mulLeft ℂ (α 0))).shift
    have h3 := (h1.map (LinearMap.mulLeft ℂ (β 0))).up
    have h4 := h2.add h3
    convert h4 using 1
    funext u
    simp only [List.ofFn_succ, List.prod_cons, LinearMap.mulLeft_apply, add_mul, smul_mul_assoc]

theorem Tm_lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u k : ℂ) (a b : Fin n) :
    Tm E (u - k) a b = u • (if a = b then (1 : A) else 0) + ((if a = b then algebraMap ℂ A (-k) else 0) + E a b) := by
  unfold Tm
  split_ifs
  · rw [Algebra.smul_def, mul_one, map_neg, map_sub]; abel
  · simp

theorem qminor_isPol {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) :
    IsPol (t + 1) (fun u => qminor E a b u) := by
  unfold qminor
  apply IsPol.sum
  intro σ _
  have h := (prod_isPol t (fun k => if a (σ k) = b k then (1 : A) else 0)
    (fun k => (if a (σ k) = b k then algebraMap ℂ A (-(k : ℂ)) else 0) + E (a (σ k)) (b k))).map
    (LinearMap.mulLeft ℂ (((Equiv.Perm.sign σ : ℤ) : A)))
  convert h using 2 with u
  simp only [LinearMap.mulLeft_apply, Tm_lin]

theorem polyVanish {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) (c : ℕ → X) (F : Finset ℂ)
    (h : ∀ u : ℂ, u ∉ F → ∑ s ∈ Finset.range d, (u ^ s) • c s = 0) : ∀ s ∈ Finset.range d, c s = 0 := by
  intro s hs
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (c s)).mp
  intro φ
  obtain ⟨p, hp⟩ : ∃ p : ℂ[X], p = ∑ j ∈ Finset.range d, Polynomial.C (φ (c j)) * Polynomial.X ^ j := ⟨_, rfl⟩
  have hroot : ∀ u : ℂ, u ∉ F → p.eval u = 0 := by
    intro u hu
    have h1 := congrArg φ (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
    rw [hp, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc _ = ∑ j ∈ Finset.range d, u ^ j * φ (c j) := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 0 := h1
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ F.finite_toSet.infinite_compl
    intro u hu
    exact hroot u hu
  have hc : p.coeff s = 0 := by rw [hp0, Polynomial.coeff_zero]
  rw [hp, Polynomial.finset_sum_coeff] at hc
  simpa [Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mp hs] using hc

theorem pow_mem {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (s : ℕ) : ∀ X ∈ G, (K ^ s) X ∈ G := by
  induction s with
  | zero => intro X hX; simpa using hX
  | succ s ih => intro X hX; rw [pow_succ']; exact hK _ (ih X hX)

theorem aeval_mem {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (p : ℂ[X]) : ∀ X ∈ G, Polynomial.aeval K p X ∈ G := by
  intro X hX
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine G.sum_mem (fun i _ => ?_)
  rw [LinearMap.smul_apply]
  exact G.smul_mem _ (Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.pow_mem G K hK i X hX)

private theorem shift_sum_lemma {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (a : ℕ → W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • shiftC a s = u • ∑ s ∈ Finset.range d, u ^ s • a s := by
  rw [Finset.sum_range_succ', Finset.smul_sum]
  simp only [shiftC, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s _ => by rw [pow_succ', mul_smul])

private theorem ite_sum_lemma_2 {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (b : ℕ → W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • (if s < d then b s else 0) = ∑ s ∈ Finset.range d, u ^ s • b s := by
  rw [Finset.sum_range_succ]
  simp only [lt_irrefl, if_false, smul_zero, add_zero]
  exact Finset.sum_congr rfl (fun s hs => by rw [if_pos (Finset.mem_range.mp hs)])

private theorem coeff_sum_lemma_3 {W : Type} [AddCommGroup W] [Module ℂ W] (d : ℕ) (P : ℂ[X])
    (hP : P.natDegree < d + 1) (Y : W) (u : ℂ) :
    ∑ s ∈ Finset.range (d + 1), u ^ s • (P.coeff s • Y) = P.eval u • Y := by
  rw [Polynomial.eval_eq_sum_range' hP, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun s _ => by rw [← mul_smul, mul_comm])

theorem ch_abstract {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (d : ℕ) (A : ℕ → W → W) (P : ℂ[X]) (hP : P.natDegree < d + 1)
    (h : ∀ (u : ℂ), ∀ X ∈ G, u • (∑ s ∈ Finset.range d, u ^ s • A s X) - ∑ s ∈ Finset.range d, u ^ s • A s (K X) =
      P.eval u • X) :
    ∀ X ∈ G, Polynomial.aeval K P X = 0 := by
  have hcoef : ∀ Y ∈ G, ∀ s ∈ Finset.range (d + 1),
      shiftC (fun t => A t Y) s - (if s < d then A s (K Y) else 0) - P.coeff s • Y = 0 := by
    intro Y hY
    apply polyVanish (d + 1) _ ∅
    intro u _
    have h1 := h u Y hY
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [shift_sum_lemma, ite_sum_lemma_2, coeff_sum_lemma_3 d P hP Y u, h1, sub_self]
  intro X hX
  rw [Polynomial.aeval_eq_sum_range' hP, LinearMap.sum_apply]
  have hterm : ∀ i ∈ Finset.range (d + 1), (P.coeff i • (K ^ i)) X =
      shiftC (fun t => A t ((K ^ i) X)) i - (if i < d then A i ((K ^ (i + 1)) X) else 0) := by
    intro i hi
    have h1 := hcoef ((K ^ i) X) (Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.pow_mem G K hK i X hX) i hi
    rw [sub_eq_zero] at h1
    rw [LinearMap.smul_apply, pow_succ']
    first
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_apply]
    exact h1.symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ, Finset.sum_sub_distrib]
  have hg : ∀ i ∈ Finset.range d, (if i < d then A i ((K ^ (i + 1)) X) else 0) =
      shiftC (fun t => A t ((K ^ (i + 1)) X)) (i + 1) := by
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
    rfl
  rw [Finset.sum_congr rfl hg, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun i => shiftC (fun t => A t ((K ^ i) X)) i)]
  simp [shiftC]

theorem sgn_mul {A : Type} [Ring A] [Algebra ℂ A] (k : ℕ) (T : A) :
    (((-1 : ℤ) ^ k : ℤ) : A) * T = ((-1 : ℂ) ^ k) • T := by
  simp [Algebra.smul_def]

section ring

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}

theorem isCov_zero : IsCov E (fun _ => (0 : A)) := by
  intro a b c
  simp

theorem isCov_add {η η' : Fin n → A} (h : IsCov E η) (h' : IsCov E η') : IsCov E (fun j => η j + η' j) := by
  intro a b c
  rw [mul_add, add_mul]
  rw [show ∀ x y z w : A, x + y - (z + w) = (x - z) + (y - w) from fun x y z w => by abel, h a b c, h' a b c]
  split_ifs <;> simp

theorem isCov_smul (k : ℂ) {η : Fin n → A} (h : IsCov E η) : IsCov E (fun j => k • η j) := by
  intro a b c
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, h a b c]
  split_ifs <;> simp

theorem isCov_D (hE : GlRel E) {η : Fin n → A} (h : IsCov E η) : IsCov E (fun j => ∑ l, E j l * η l) := by
  intro a b c
  have key : ∀ l, E a b * (E c l * η l) - E c l * η l * E a b =
      (E a b * E c l - E c l * E a b) * η l + E c l * (E a b * η l - η l * E a b) := by
    intro l; noncomm_ring
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [key, hE a b c, h a b]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · simp [hbc, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end ring

section cov

variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

def Th (u : ℂ) : Module.End ℂ (Fin (N + 1) → V) :=
  LinearMap.pi fun x => ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) •
    (qminor E a.succAbove x.succAbove u ∘ₗ LinearMap.proj a)

theorem Th_apply (u : ℂ) (X : Fin (N + 1) → V) (x : Fin (N + 1)) :
    Th E u X x = ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • qminor E a.succAbove x.succAbove u (X a) := by
  simp [Th, LinearMap.sum_apply]

def EE : Module.End ℂ (Fin (N + 1) → V) := LinearMap.pi fun j => ∑ l, E j l ∘ₗ LinearMap.proj l

theorem EE_apply (X : Fin (N + 1) → V) (j : Fin (N + 1)) : EE E X j = ∑ l, E j l (X l) := by
  simp [EE, LinearMap.sum_apply]

def Gd (v : V) : Submodule ℂ (Fin (N + 1) → V) where
  carrier := {X | ∃ η : Fin (N + 1) → Module.End ℂ V, IsCov E η ∧ ∀ j, X j = η j v}
  add_mem' := by
    rintro X Y ⟨η, hη, hX⟩ ⟨η', hη', hY⟩
    exact ⟨_, isCov_add hη hη', fun j => by simp [hX, hY]⟩
  zero_mem' := ⟨_, isCov_zero, fun j => by simp⟩
  smul_mem' := by
    rintro k X ⟨η, hη, hX⟩
    exact ⟨_, isCov_smul k hη, fun j => by simp [hX]⟩

theorem mem_Gd {v : V} {X : Fin (N + 1) → V} :
    X ∈ Gd E v ↔ ∃ η : Fin (N + 1) → Module.End ℂ V, IsCov E η ∧ ∀ j, X j = η j v := by
  exact Iff.rfl

theorem EE_mem (hE : GlRel E) {v : V} {X : Fin (N + 1) → V} (hX : X ∈ Gd E v) : EE E X ∈ Gd E v := by
  obtain ⟨η, hη, hXη⟩ := (mem_Gd E).mp hX
  refine (mem_Gd E).mpr ⟨fun j => ∑ l, E j l * η l, isCov_D hE hη, fun j => ?_⟩
  rw [EE_apply]
  first
    | (simp [hXη]; done)
    | (simp [hXη, Module.End.mul_apply]; done)
    | (simp [hXη, LinearMap.mul_apply]; done)

theorem Tm_apply (w : ℂ) (j l : Fin (N + 1)) (y : V) :
    Tm E w j l y = (if j = l then w • y else 0) + E j l y := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem comat (hE : GlRel E) (u : ℂ) (X : Fin (N + 1) → V) (i : Fin (N + 1)) :
    Th E u ((u - (N : ℂ)) • X + EE E X) i = qdet E u (X i) := by
  have h : ∀ l, ∑ j : Fin (N + 1), ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ))) •
      qminor E j.succAbove i.succAbove u (Tm E (u - (N : ℂ)) j l (X l)) = if i = l then qdet E u (X l) else 0 := by
    intro l
    have := congrArg (fun T : Module.End ℂ V => T (X l))
      (qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) N E hE u i l)
    simp only [sgn_mul, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [apply_ite (fun T : Module.End ℂ V => T (X l)), LinearMap.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])
  have h2 : ∑ l, (if i = l then qdet E u (X l) else 0) = qdet E u (X i) := by simp
  rw [← h2, ← Finset.sum_congr rfl (fun l _ => h l), Finset.sum_comm, Th_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.smul_sum, ← map_sum]
  congr 2
  simp only [Tm_apply, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply,
    Pi.smul_apply, EE_apply]

theorem detCov (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) {X : Fin (N + 1) → V}
    (hX : X ∈ Gd E v) (u : ℂ) (x : Fin (N + 1)) :
    qdet E u (X x) = cpol m u • X x + Th E u X x := by
  obtain ⟨η, hη, hX⟩ := hX
  have h := congrArg (fun T : Module.End ℂ V => T v)
    (QuantumMinorCommutation.minorCov_gen E hE η hη id id x (fun k => Fin.succAbove_ne x k) u)
  simp only [id, Function.id_comp, sgn_mul, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at h
  have hq : qminor E id id u v = cpol m u • v := mem_CapSp.1 hv u
  rw [hq, map_smul, sub_eq_iff_eq_add'] at h
  rw [Th_apply, hX x]
  refine h.trans ?_
  congr 1
  exact Finset.sum_congr rfl (fun l _ => by rw [add_comm, hX l])

end cov

theorem eval_prod_lin {ι : Type} (S : Finset ι) (m : ι → ℂ) (u : ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).eval u = ∏ j ∈ S, (u + m j) := by
  simp [Polynomial.eval_prod]

theorem deg_prod_lin {ι : Type} (S : Finset ι) (m : ι → ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  simp [Polynomial.natDegree_X_add_C]

theorem basis_mul {N : ℕ} (m : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    ∃ w : ℂ, ((Polynomial.X : ℂ[X]) + C (m i)) * Lagrange.basis Finset.univ (fun j => -m j) i =
      C w * ∏ j, ((Polynomial.X : ℂ[X]) + C (m j)) := by
  refine ⟨∏ j ∈ Finset.univ.erase i, (-m i - -m j)⁻¹, ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (Polynomial.X : ℂ[X]) + C (m j)) (Finset.mem_univ i)]
  have hb : Lagrange.basis Finset.univ (fun j => -m j) i =
      C (∏ j ∈ Finset.univ.erase i, (-m i - -m j)⁻¹) *
        ∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j)) := by
    rw [Lagrange.basis, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [Lagrange.basisDivisor, map_neg, sub_neg_eq_add]
  rw [hb]
  beta_reduce
  ring

section main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

def KK : Module.End ℂ (Fin (N + 1) → V) := ((N : ℂ) + 1) • 1 - EE E

theorem KK_apply (X : Fin (N + 1) → V) : KK E X = ((N : ℂ) + 1) • X - EE E X := by
  first | rfl | (simp [KK]; done)

theorem KK_mem (hE : GlRel E) {v : V} {X : Fin (N + 1) → V} (hX : X ∈ Gd E v) : KK E X ∈ Gd E v := by
  rw [KK_apply]
  exact (Gd E v).sub_mem ((Gd E v).smul_mem _ hX) (EE_mem E hE hX)

theorem star (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) {X : Fin (N + 1) → V}
    (hX : X ∈ Gd E v) (u : ℂ) : u • Th E u X - Th E u (KK E X) = cpol m u • X := by
  funext x
  have h1 := comat E hE u X x
  have h2 := detCov E hE hv hX u x
  have lin : (u • Th E u X - Th E u (KK E X)) x = Th E u ((u - (N : ℂ)) • X + EE E X) x - Th E u X x := by
    rw [KK_apply]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    first
      | module
      | (simp only [sub_smul, add_smul, one_smul]; abel)
  rw [lin, h1, h2, Pi.smul_apply, add_sub_cancel_right]

theorem Th_pol : ∃ A : ℕ → (Fin (N + 1) → V) → (Fin (N + 1) → V), ∀ (u : ℂ) (X : Fin (N + 1) → V),
    Th E u X = ∑ s ∈ Finset.range (N + 1), u ^ s • A s X := by
  have hq : ∀ a x : Fin (N + 1), ∃ c : ℕ → Module.End ℂ V, ∀ u : ℂ,
      qminor E a.succAbove x.succAbove u = ∑ s ∈ Finset.range (N + 1), (u ^ s) • c s :=
    fun a x => qminor_isPol E _ _
  choose c hc using hq
  refine ⟨fun s X x => ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • c a x s (X a), fun u X => ?_⟩
  funext x
  rw [Th_apply]
  simp only [hc, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ => smul_comm _ _ _))

theorem charId (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) :
    ∀ X ∈ Gd E v, Polynomial.aeval (KK E) (∏ j, ((Polynomial.X : ℂ[X]) + C (m j))) X = 0 := by
  obtain ⟨A, hA⟩ := Th_pol E
  intro X hX
  refine ch_abstract (Gd E v) (KK E) (fun Y hY => KK_mem E hE hY) (N + 1) A _ ?_ (fun u Y hY => ?_) X hX
  · have h := deg_prod_lin (Finset.univ : Finset (Fin (N + 1))) m
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  · rw [← hA, ← hA, star E hE hv hY u, eval_prod_lin]
    rfl

theorem Th_eigen (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) (i : Fin (N + 1))
    {Y : Fin (N + 1) → V} (hY : Y ∈ Gd E v) (hK : KK E Y = (-m i) • Y) (u : ℂ) :
    Th E u Y = (∏ j ∈ Finset.univ.erase i, (u + m j)) • Y := by
  have key : ∀ w : ℂ, w ≠ -m i → Th E w Y = (∏ j ∈ Finset.univ.erase i, (w + m j)) • Y := by
    intro w hw
    have h := star E hE hv hY w
    rw [hK, map_smul, ← sub_smul] at h
    have hne : w - -m i ≠ 0 := sub_ne_zero.mpr hw
    have hc : cpol m w = (w - -m i) * ∏ j ∈ Finset.univ.erase i, (w + m j) := by
      rw [cpol, ← Finset.mul_prod_erase Finset.univ (fun j => w + m j) (Finset.mem_univ i), sub_neg_eq_add]
    rw [hc, mul_smul] at h
    exact smul_right_injective (Fin (N + 1) → V) hne h
  obtain ⟨A, hA⟩ := Th_pol E
  have hQ : (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).natDegree < N + 1 := by
    have h := deg_prod_lin (Finset.univ.erase i) m
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h
    omega
  have hev : ∀ w : ℂ, ∏ j ∈ Finset.univ.erase i, (w + m j) =
      ∑ s ∈ Finset.range (N + 1),
        (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).coeff s * w ^ s := by
    intro w
    rw [← eval_prod_lin, Polynomial.eval_eq_sum_range' hQ]
  have hvan := polyVanish (N + 1)
    (fun s => A s Y - (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).coeff s • Y) {-m i} (by
      intro w hw
      have h1 := key w (by simpa using hw)
      rw [hA, hev, Finset.sum_smul] at h1
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero, h1]
      exact Finset.sum_congr rfl (fun s _ => by rw [mul_comm, mul_smul]))
  rw [hA, hev, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have h2 := hvan s hs
  rw [sub_eq_zero] at h2
  rw [h2, mul_comm, mul_smul]

theorem covUp_succ (η : Fin (N + 1) → Module.End ℂ V) (hE : GlRel E) (hη : IsCov E η) (m : Fin (N + 1) → ℂ)
    (hm : Function.Injective m) (v : V) (hv : v ∈ CapSp E m) :
    ∃ Ψ : Fin (N + 1) → Fin (N + 1) → V,
      (∀ x, ∑ i, Ψ i x = η x v) ∧
      (∀ i x, Ψ i x ∈ CapSp E (Function.update m i (m i + 1))) ∧
      ∀ (i x : Fin (N + 1)) (u : ℂ),
        ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • qminor E a.succAbove x.succAbove u (Ψ i a) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Ψ i x := by
  obtain ⟨Z, hZdef⟩ : ∃ Z : Fin (N + 1) → V, Z = fun x => η x v := ⟨_, rfl⟩
  have hZ : Z ∈ Gd E v := (mem_Gd E).mpr ⟨η, hη, fun j => by rw [hZdef]⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (N + 1) → Fin (N + 1) → V,
      Y = fun i => Polynomial.aeval (KK E) (Lagrange.basis Finset.univ (fun j => -m j) i) Z := ⟨_, rfl⟩
  have hY : ∀ i, Y i ∈ Gd E v := by
    intro i
    rw [hYdef]
    exact aeval_mem (Gd E v) (KK E) (fun W hW => KK_mem E hE hW) _ Z hZ
  have hKY : ∀ i, KK E (Y i) = (-m i) • Y i := by
    intro i
    obtain ⟨w, hw⟩ := basis_mul m i
    have h1 : Polynomial.aeval (KK E)
        (((Polynomial.X : ℂ[X]) + C (m i)) * Lagrange.basis Finset.univ (fun j => -m j) i) Z = 0 := by
      rw [hw, map_mul, Polynomial.aeval_C]
      first
        | rw [Module.End.mul_apply, charId E hE hv Z hZ, map_zero]
        | rw [LinearMap.mul_apply, charId E hE hv Z hZ, map_zero]
    rw [map_mul] at h1
    first
      | rw [Module.End.mul_apply] at h1
      | rw [LinearMap.mul_apply] at h1
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.algebraMap_end_apply] at h1
    rw [hYdef, neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Y, fun x => ?_, fun i x => ?_, fun i x u => ?_⟩
  · have hs : ∑ i, Lagrange.basis Finset.univ (fun j => -m j) i = 1 :=
      Lagrange.sum_basis (fun a _ b _ h => hm (neg_injective h)) Finset.univ_nonempty
    have hsum : ∑ i, Y i = Z := by
      rw [hYdef, ← LinearMap.sum_apply, ← map_sum, hs, map_one]
      rfl
    have h1 := congrFun hsum x
    rw [Finset.sum_apply] at h1
    rw [h1, hZdef]
  · rw [CapSp, Submodule.mem_iInf]
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
    first
      | rw [Module.End.one_apply]
      | rw [LinearMap.one_apply]
    rw [detCov E hE hv (hY i) w x, Th_eigen E hE hv i (hY i) (hKY i) w, Pi.smul_apply, ← add_smul]
    congr 1
    have hP : ∏ j ∈ Finset.univ.erase i, (w + Function.update m i (m i + 1) j) =
        ∏ j ∈ Finset.univ.erase i, (w + m j) :=
      Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hi : Function.update m i (m i + 1) i = m i + 1 := by simp
    have e1 := Finset.mul_prod_erase Finset.univ (fun j => w + m j) (Finset.mem_univ i)
    have e2 := Finset.mul_prod_erase Finset.univ (fun j => w + Function.update m i (m i + 1) j) (Finset.mem_univ i)
    beta_reduce at e1 e2
    rw [cpol, cpol, ← e1, ← e2, hP, hi]
    ring
  · rw [← Th_apply, Th_eigen E hE hv i (hY i) (hKY i) u, Pi.smul_apply]

end main

end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter

theorem Formalism.FourierDecayAlt.P.quantum_minor_polynomial : Formalism.FourierDecayAlt.Qr.QminorPoly := by
  intro A _ _ n t E a b
  exact Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.qminor_isPol E a b

theorem Formalism.FourierDecayAlt.P.polynomial_vanishing : Formalism.FourierDecayAlt.Qr.PolyVanish := by
  intro X _ _ d c F h
  exact Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.polyVanish d c F h

theorem Formalism.FourierDecayAlt.P.covariant_raising : Formalism.FourierDecayAlt.Qr.CovUp := by
  intro V _ _ n E η hE hη m hm v hv
  cases n with
  | zero => exact ⟨fun i => i.elim0, fun x => x.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ N =>
    have hs : ∀ a : Fin (N + 1), (Formalism.FourierDecayAlt.Q.skip1 a : Fin N → Fin (N + 1)) = a.succAbove := by
      intro a
      funext j
      have hc : (j.castSucc < a ↔ (j : ℕ) < a) := by rw [Fin.lt_def, Fin.coe_castSucc]
      unfold Formalism.FourierDecayAlt.Q.skip1 Fin.succAbove
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hc.mpr h1) h2
      · exact absurd (hc.mp h2) h1
      · rfl
    obtain ⟨Ψ, h1, h2, h3⟩ := Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.covUp_succ E η hE hη m hm v hv
    refine ⟨Ψ, h1, h2, fun i x u => ?_⟩
    simp only [hs]
    exact h3 i x u
