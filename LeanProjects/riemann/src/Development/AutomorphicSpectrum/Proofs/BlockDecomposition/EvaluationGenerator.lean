import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult.HCD

open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def adZ (Z : Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ Z - LinearMap.mulRight ℂ Z

theorem adZ_apply (Z T : Module.End ℂ V) : adZ Z T = Z * T - T * Z := rfl

theorem adZ_mul (Z S T : Module.End ℂ V) : adZ Z (S * T) = adZ Z S * T + S * adZ Z T := by
  simp only [adZ_apply]; noncomm_ring

def JJ (N : Submodule ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {T | ∀ x, T x ∈ N}
  add_mem' ha hb x := N.add_mem (ha x) (hb x)
  zero_mem' _ := N.zero_mem
  smul_mem' c _ h x := N.smul_mem c (h x)

theorem JJ_mul (N : Submodule ℂ V) {T : Module.End ℂ V} (h : T ∈ JJ N) (S : Module.End ℂ V) :
    T * S ∈ JJ N := fun x => h (S x)

theorem adZ_JJ {Z : Module.End ℂ V} {N : Submodule ℂ V} (hZ : ∀ y ∈ N, Z y ∈ N) :
    JJ N ≤ (JJ N).comap (adZ Z) := by
  intro T hT x
  exact N.sub_mem (hZ _ (hT x)) (hT _)

def PP (Z : Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ k : ℕ, adZ Z T = ((k : ℂ) + 1) • T}

theorem congruenceCondition_mul {Z T S : Module.End ℂ V} (hT : T ∈ PP Z) {m : ℕ} (hS : adZ Z S = (m : ℂ) • S) :
    T * S ∈ PP Z := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨k, hk⟩ := h
    refine Submodule.subset_span ⟨k + m, ?_⟩
    rw [adZ_mul, hk, hS, smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1; push_cast; ring
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact (PP Z).add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact (PP Z).smul_mem c hx

theorem mem_JJ_of {Z : Module.End ℂ V} {N : Submodule ℂ V} (hZ : ∀ y ∈ N, Z y ∈ N)
    {t p : Module.End ℂ V} (ht : adZ Z t = 0) (hp : p ∈ PP Z) (h : t - p ∈ JJ N) : t ∈ JJ N := by
  set D : Module.End ℂ (Module.End ℂ V ⧸ JJ N) := (JJ N).mapQ (JJ N) (adZ Z) (adZ_JJ hZ) with hD
  have hd := iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep D) 0
  have h1 : (JJ N).mkQ t ∈ D.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, ht]
    rfl
  have h2 : (JJ N).mkQ p ∈ ⨆ j, ⨆ (_ : j ≠ (0 : ℂ)), D.eigenspace j := by
    clear h
    induction hp using Submodule.span_induction with
    | mem T h =>
      obtain ⟨k, hk⟩ := h
      refine Submodule.mem_iSup_of_mem ((k : ℂ) + 1) (Submodule.mem_iSup_of_mem
        (Nat.cast_add_one_ne_zero k) ?_)
      rw [Module.End.mem_eigenspace_iff, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, hk]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h3 : (JJ N).mkQ t = (JJ N).mkQ p := (Submodule.Quotient.eq _).mpr h
  rw [← h3] at h2
  have := (Submodule.disjoint_def.mp hd) _ h1 h2
  exact (Submodule.Quotient.mk_eq_zero _).mp this

end Gen

section Mod

variable {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
  {E1 E2 : Fin n → Fin n → Module.End ℂ V}

def op (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Bool × Fin n × Fin n) : Module.End ℂ V :=
  if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

theorem evaluation_generator (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Bool × Fin n × Fin n) :
    ev2 E1 E2 (FreeAlgebra.ι ℂ x) = op E1 E2 x := by
  simp [ev2, op]

theorem evB_ι_of_eq (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    {x : Bool × Fin n × Fin n} (h : lev x.2.1 = lev x.2.2) :
    evB lev E1 E2 (FreeAlgebra.ι ℂ x) = op E1 E2 x := by
  simp [evB, op, h]

theorem evB_ι_of_ne (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    {x : Bool × Fin n × Fin n} (h : lev x.2.1 ≠ lev x.2.2) :
    evB lev E1 E2 (FreeAlgebra.ι ℂ x) = 0 := by
  simp [evB, h]

def NV (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ (l : Lt n) (w : V), inUL lev l ∧ y = Tl E1 E2 l w}

theorem mem_NV_Tl {l : Lt n} (h : inUL lev l) (w : V) : Tl E1 E2 l w ∈ NV lev E1 E2 :=
  Submodule.subset_span ⟨l, w, h, rfl⟩

theorem mem_NV (hm : Monotone lev) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    {x : Bool × Fin n × Fin n} (h : lev x.2.1 < lev x.2.2) (w : V) :
    op E1 E2 x w ∈ NV lev E1 E2 := by
  obtain ⟨s, a, b⟩ := x
  have hab : a < b := hm.reflect_lt h
  have hK : (E1 a b + E2 a b) w ∈ NV lev E1 E2 :=
    mem_NV_Tl (E1 := E1) (E2 := E2) (l := (true, ⟨(a, b), hab⟩)) h w
  have hP : (E1 a b - E2 a b) w ∈ NV lev E1 E2 :=
    mem_NV_Tl (E1 := E1) (E2 := E2) (l := (false, ⟨(a, b), hab⟩)) h w
  have h1 := (NV lev E1 E2).smul_mem (1 / 2 : ℂ) ((NV lev E1 E2).add_mem hK hP)
  have h2 := (NV lev E1 E2).smul_mem (1 / 2 : ℂ) ((NV lev E1 E2).sub_mem hK hP)
  cases s
  · convert h2 using 1
    simp only [op, LinearMap.add_apply, LinearMap.sub_apply]
    simp only [Bool.false_eq_true, if_false]
    rw [show E1 a b w + E2 a b w - (E1 a b w - E2 a b w) = (2 : ℂ) • E2 a b w by
      rw [two_smul]; abel, smul_smul]
    norm_num
  · convert h1 using 1
    simp only [op, LinearMap.add_apply, LinearMap.sub_apply, if_true]
    rw [show E1 a b w + E2 a b w + (E1 a b w - E2 a b w) = (2 : ℂ) • E1 a b w by
      rw [two_smul]; abel, smul_smul]
    norm_num

theorem sum_of_mem_NV {y : V} (hy : y ∈ NV lev E1 E2) :
    ∃ w : Lt n → V, y = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0 := by
  classical
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨l, w, hl, rfl⟩ := h
    refine ⟨Pi.single l w, ?_⟩
    rw [Finset.sum_eq_single l]
    · simp [hl]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    refine ⟨w + w', ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  | smul c x _ hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨c • w, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp

def hh (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((lev c : ℕ) : ℂ) • E c c

theorem hh_comm (lev : Fin n → ℕ) {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    hh lev E * E a b - E a b * hh lev E = (((lev a : ℕ) : ℂ) - ((lev b : ℕ) : ℂ)) • E a b := by
  have h : ∀ c : Fin n, ((lev c : ℕ) : ℂ) • E c c * E a b - E a b * ((lev c : ℕ) : ℂ) • E c c =
      (if c = a then ((lev a : ℕ) : ℂ) • E a b else 0) -
        (if c = b then ((lev b : ℕ) : ℂ) • E a b else 0) := by
    intro c
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hE c c a b, smul_sub]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · by_cases h : b = c
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [hh, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_smul]

def ZZ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((lev c : ℕ) : ℂ) • (E1 c c + E2 c c)

theorem ZZ_eq (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    ZZ lev E1 E2 = hh lev E1 + hh lev E2 := by
  simp only [ZZ, hh, smul_add, Finset.sum_add_distrib]

theorem ZZ_comm (h : PairRel E1 E2) (x : Bool × Fin n × Fin n) :
    adZ (ZZ lev E1 E2) (op E1 E2 x) =
      (((lev x.2.1 : ℕ) : ℂ) - ((lev x.2.2 : ℕ) : ℂ)) • op E1 E2 x := by
  obtain ⟨s, a, b⟩ := x
  rw [adZ_apply, ZZ_eq]
  cases s
  · have hc : Commute (hh lev E1) (E2 a b) :=
      Commute.sum_left _ _ _ fun c _ => (h.2.2 c c a b).smul_left _
    have := hh_comm lev h.2.1 a b
    simp only [op, Bool.false_eq_true, if_false]
    rw [add_mul, mul_add, hc.eq, ← this]; abel
  · have hc : Commute (hh lev E2) (E1 a b) :=
      Commute.sum_left _ _ _ fun c _ => (h.2.2 a b c c).symm.smul_left _
    have := hh_comm lev h.1 a b
    simp only [op, if_true]
    rw [add_mul, mul_add, hc.eq, ← this]; abel

theorem Tl_comm (h : PairRel E1 E2) (l : Lt n) :
    adZ (ZZ lev E1 E2) (Tl E1 E2 l) =
      (((lev l.2.1.1 : ℕ) : ℂ) - ((lev l.2.1.2 : ℕ) : ℂ)) • Tl E1 E2 l := by
  obtain ⟨s, i⟩ := l
  have h1 := ZZ_comm (lev := lev) h (true, i.1.1, i.1.2)
  have h2 := ZZ_comm (lev := lev) h (false, i.1.1, i.1.2)
  simp only [op, if_true, Bool.false_eq_true, if_false] at h1 h2
  cases s
  · simp only [Tl, Ts, Bool.false_eq_true, if_false, map_sub, h1, h2, smul_sub]
  · simp only [Tl, Ts, if_true, map_add, h1, h2, smul_add]

theorem ZZ_NV (h : PairRel E1 E2) (y : V) (hy : y ∈ NV lev E1 E2) :
    ZZ lev E1 E2 y ∈ NV lev E1 E2 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, w, hl, rfl⟩ := hy
    have h1 := LinearMap.congr_fun (Tl_comm (lev := lev) h l) w
    simp only [adZ_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1
    rw [sub_eq_iff_eq_add.mp h1]
    exact (NV lev E1 E2).add_mem ((NV lev E1 E2).smul_mem _ (mem_NV_Tl hl _)) (mem_NV_Tl hl _)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (NV lev E1 E2).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (NV lev E1 E2).smul_mem c hx

theorem adZ_evB (h : PairRel E1 E2) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    adZ (ZZ lev E1 E2) (evB lev E1 E2 b) = 0 := by
  induction b using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes, adZ_apply, Algebra.commutes, sub_self]
  | grade1 x =>
    by_cases hl : lev x.2.1 = lev x.2.2
    · rw [evB_ι_of_eq lev E1 E2 hl, ZZ_comm h, hl, sub_self, zero_smul]
    · rw [evB_ι_of_ne lev E1 E2 hl, map_zero]
  | mul a b ha hb => rw [map_mul, adZ_mul, ha, hb]; simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

def brA (y p : Bool × Fin n × Fin n) : FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  if y.1 = p.1 ∧ y.2.2 = p.2.1 then FreeAlgebra.ι ℂ (y.1, y.2.1, p.2.2) else 0

def brB (y p : Bool × Fin n × Fin n) : FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  if y.1 = p.1 ∧ p.2.2 = y.2.1 then FreeAlgebra.ι ℂ (y.1, p.2.1, y.2.2) else 0

theorem op_br (h : PairRel E1 E2) (y p : Bool × Fin n × Fin n) :
    op E1 E2 y * op E1 E2 p - op E1 E2 p * op E1 E2 y = ev2 E1 E2 (brA y p) - ev2 E1 E2 (brB y p) := by
  obtain ⟨s, a, b⟩ := y
  obtain ⟨t, c, d⟩ := p
  cases s <;> cases t
  · have := h.2.1 a b c d
    have e : ∀ a b, op E1 E2 (false, a, b) = E2 a b := fun _ _ => by simp [op]
    rw [e a b, e c d, this]
    simp only [brA, brB, true_and]
    congr 1 <;> split_ifs <;> simp [evaluation_generator, op]
  · have := (h.2.2 c d a b).eq
    simp [brA, brB, op, this]
  · have := (h.2.2 a b c d).eq
    simp [brA, brB, op, this]
  · have := h.1 a b c d
    have e : ∀ a b, op E1 E2 (true, a, b) = E1 a b := fun _ _ => by simp [op]
    rw [e a b, e c d, this]
    simp only [brA, brB, true_and]
    congr 1 <;> split_ifs <;> simp [evaluation_generator, op]

end Mod

inductive Low (lev : Fin n → ℕ) : FreeAlgebra ℂ (Bool × Fin n × Fin n) → Prop
  | one : Low lev 1
  | mul (u) (p : Bool × Fin n × Fin n) : Low lev u → lev p.2.2 ≤ lev p.2.1 →
      Low lev (u * FreeAlgebra.ι ℂ p)
  | add (u v) : Low lev u → Low lev v → Low lev (u + v)
  | smul (c : ℂ) (u) : Low lev u → Low lev (c • u)

theorem Low.zero (lev : Fin n → ℕ) : Low lev (0 : FreeAlgebra ℂ (Bool × Fin n × Fin n)) := by
  simpa using Low.smul (0 : ℂ) (1 : FreeAlgebra ℂ (Bool × Fin n × Fin n)) Low.one

theorem Low.levi {lev : Fin n → ℕ} {u : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hu : Low lev u) :
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
        ev2 E1 E2 u - evB lev E1 E2 b ∈ PP (ZZ lev E1 E2) := by
  induction hu with
  | one => exact ⟨1, fun V _ _ E1 E2 _ => by simp⟩
  | mul u p _ hp ih =>
    obtain ⟨b, hb⟩ := ih
    have key : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
        adZ (ZZ lev E1 E2) (op E1 E2 p) = (((lev p.2.1 - lev p.2.2 : ℕ)) : ℂ) • op E1 E2 p := by
      intro V _ _ E1 E2 hE
      rw [ZZ_comm hE, Nat.cast_sub hp]
    rcases eq_or_lt_of_le hp with h | h
    · refine ⟨b * FreeAlgebra.ι ℂ p, fun V _ _ E1 E2 hE => ?_⟩
      have := congruenceCondition_mul (hb V E1 E2 hE) (key V E1 E2 hE)
      rw [map_mul, map_mul, evaluation_generator, evB_ι_of_eq lev E1 E2 h.symm, ← sub_mul]
      exact this
    · refine ⟨0, fun V _ _ E1 E2 hE => ?_⟩
      have h1 := congruenceCondition_mul (hb V E1 E2 hE) (key V E1 E2 hE)
      have h2 : evB lev E1 E2 b * op E1 E2 p ∈ PP (ZZ lev E1 E2) := by
        refine Submodule.subset_span ⟨lev p.2.1 - lev p.2.2 - 1, ?_⟩
        rw [adZ_mul, adZ_evB hE, key V E1 E2 hE, zero_mul, zero_add, mul_smul_comm]
        congr 1
        have : lev p.2.1 - lev p.2.2 = lev p.2.1 - lev p.2.2 - 1 + 1 := by omega
        exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) this
      have h3 := (PP (ZZ lev E1 E2)).add_mem h1 h2
      rw [map_mul, evaluation_generator, map_zero, sub_zero]
      simpa [sub_mul] using h3
  | add u v _ _ hu hv =>
    obtain ⟨b, hb⟩ := hu
    obtain ⟨b', hb'⟩ := hv
    refine ⟨b + b', fun V _ _ E1 E2 hE => ?_⟩
    have := (PP (ZZ lev E1 E2)).add_mem (hb V E1 E2 hE) (hb' V E1 E2 hE)
    rw [map_add, map_add]
    convert this using 1; abel
  | smul c u _ hu =>
    obtain ⟨b, hb⟩ := hu
    refine ⟨c • b, fun V _ _ E1 E2 hE => ?_⟩
    rw [map_smul, map_smul, ← smul_sub]
    exact (PP (ZZ lev E1 E2)).smul_mem c (hb V E1 E2 hE)

def Red (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∃ u, Low lev u ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ev2 E1 E2 a - ev2 E1 E2 u ∈ JJ (NV lev E1 E2)

variable {lev : Fin n → ℕ}

theorem Red.add {a a' : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Red lev a) (h' : Red lev a') :
    Red lev (a + a') := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := h'
  refine ⟨u + u', Low.add _ _ hu hu', fun V _ _ E1 E2 hE => ?_⟩
  have := (JJ (NV lev E1 E2)).add_mem (h V E1 E2 hE) (h' V E1 E2 hE)
  rw [map_add, map_add]
  convert this using 1; abel

theorem Red.smul (c : ℂ) {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Red lev a) :
    Red lev (c • a) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨c • u, Low.smul _ _ hu, fun V _ _ E1 E2 hE => ?_⟩
  rw [map_smul, map_smul, ← smul_sub]
  exact (JJ (NV lev E1 E2)).smul_mem c (h V E1 E2 hE)

theorem Red.of_low {u : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hu : Low lev u) : Red lev u :=
  ⟨u, hu, fun V _ _ E1 E2 _ => by simp [JJ]⟩

theorem Red.congr {a a' : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Red lev a)
    (he : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ev2 E1 E2 a' = ev2 E1 E2 a) :
    Red lev a' := by
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, fun V _ _ E1 E2 hE => he V E1 E2 hE ▸ h V E1 E2 hE⟩

theorem Red.mul_low {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Red lev a)
    (p : Bool × Fin n × Fin n) (hp : lev p.2.2 ≤ lev p.2.1) : Red lev (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨_, Low.mul u p hu hp, fun V _ _ E1 E2 hE => ?_⟩
  rw [map_mul, map_mul, ← sub_mul]
  exact JJ_mul _ (h V E1 E2 hE) _

theorem Low.red_mul (hm : Monotone lev) {u : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hu : Low lev u) :
    ∀ p : Bool × Fin n × Fin n, Red lev (u * FreeAlgebra.ι ℂ p) := by
  induction hu with
  | one =>
    intro p
    rcases le_or_gt (lev p.2.2) (lev p.2.1) with h | h
    · exact Red.of_low (Low.mul _ p Low.one h)
    · refine ⟨0, Low.zero lev, fun V _ _ E1 E2 _ => ?_⟩
      rw [one_mul, map_zero, sub_zero, evaluation_generator]
      exact fun x => mem_NV hm E1 E2 h x
  | mul u y _ hy ih =>
    intro p
    have h1 : Red lev (u * brA y p) := by
      unfold brA
      split_ifs
      · exact ih _
      · rw [mul_zero]; exact Red.of_low (Low.zero lev)
    have h2 : Red lev (u * brB y p) := by
      unfold brB
      split_ifs
      · exact ih _
      · rw [mul_zero]; exact Red.of_low (Low.zero lev)
    refine ((((ih p).mul_low y hy).add h1).add (h2.smul (-1))).congr fun V _ _ E1 E2 hE => ?_
    have h := sub_eq_iff_eq_add.mp (op_br hE y p)
    simp only [map_add, map_mul, evaluation_generator, map_smul, mul_assoc, h]
    simp only [mul_add, mul_sub, neg_smul, one_smul]
    abel
  | add u v _ _ hu hv => intro p; rw [add_mul]; exact (hu p).add (hv p)
  | smul c u _ hu => intro p; rw [smul_mul_assoc]; exact (hu p).smul c

theorem Red.mul_ι (hm : Monotone lev) {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Red lev a)
    (p : Bool × Fin n × Fin n) : Red lev (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := hu.red_mul hm p
  refine ⟨u', hu', fun V _ _ E1 E2 hE => ?_⟩
  have := (JJ (NV lev E1 E2)).add_mem (JJ_mul _ (h V E1 E2 hE) (ev2 E1 E2 (FreeAlgebra.ι ℂ p)))
    (h' V E1 E2 hE)
  rw [map_mul] at this ⊢
  convert this using 1
  rw [sub_mul]; abel

theorem red_all (hm : Monotone lev) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Red lev a := by
  have : ∀ z, Red lev z → Red lev (z * a) := by
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro z hz
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact hz.smul r
    | grade1 p => exact fun z hz => hz.mul_ι hm p
    | mul a b ha hb => intro z hz; rw [← mul_assoc]; exact hb _ (ha _ hz)
    | add a b ha hb => intro z hz; rw [mul_add]; exact (ha _ hz).add (hb _ hz)
  simpa using this 1 (Red.of_low Low.one)

theorem hcDec2 : HCDec2 := by
  intro n lev a hm ha
  obtain ⟨u, hu, h⟩ := red_all hm a
  obtain ⟨b, hb⟩ := hu.levi
  refine ⟨b, fun V _ _ E1 E2 hE x => ?_⟩
  have h0 : adZ (ZZ lev E1 E2) (ev2 E1 E2 a - evB lev E1 E2 b) = 0 := by
    rw [map_sub, adZ_evB hE, sub_zero, adZ_apply, sub_eq_zero]
    exact (Commute.sum_left _ _ _ fun c _ => (ha V E1 E2 hE c c).smul_left _).eq
  have h1 := mem_JJ_of (ZZ_NV hE) h0 (hb V E1 E2 hE) (by simpa using h V E1 E2 hE)
  exact sum_of_mem_NV (h1 x)

end GlobalTheory.CompanionTheory.PairMult.HCD
