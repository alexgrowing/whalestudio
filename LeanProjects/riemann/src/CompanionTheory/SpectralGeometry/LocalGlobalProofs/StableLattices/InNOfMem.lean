import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

namespace GlobalTheory.CompanionTheory.HCdecomp

open Formalism.REAL (GlRel)
open CompanionTheory.D.LK

variable {n : ℕ}

section Mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def NV (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V :=
  ⨆ i : Pos n, LinearMap.range (E i.1.1 i.1.2)

theorem mem_NV (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n} (h : a < b) (w : V) :
    E a b w ∈ NV E :=
  Submodule.mem_iSup_of_mem (⟨(a, b), h⟩ : Pos n) ⟨w, rfl⟩

theorem inN_of_mem (E : Fin n → Fin n → Module.End ℂ V) {y : V} (hy : y ∈ NV E) :
    InN (allT n) E y := by
  classical
  refine Submodule.iSup_induction _ (motive := fun y => InN (allT n) E y) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    refine ⟨Pi.single i w, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp [cpt]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · exact ⟨0, by simp⟩
  · rintro x y ⟨w, rfl⟩ ⟨w', rfl⟩
    refine ⟨w + w', ?_⟩
    simp [cpt, Finset.sum_add_distrib]

def JJ (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {T | ∀ x, T x ∈ NV E}
  add_mem' ha hb x := (NV E).add_mem (ha x) (hb x)
  zero_mem' _ := (NV E).zero_mem
  smul_mem' c _ h x := (NV E).smul_mem c (h x)

theorem JJ_mul (E : Fin n → Fin n → Module.End ℂ V) {T : Module.End ℂ V} (h : T ∈ JJ E)
    (S : Module.End ℂ V) : T * S ∈ JJ E := fun x => h (S x)

def HH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V := ∑ c : Fin n, ((c : ℕ) : ℂ) • E c c

theorem HH_comm {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    HH E * E a b - E a b * HH E = (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) • E a b := by
  have h : ∀ c : Fin n, ((c : ℕ) : ℂ) • E c c * E a b - E a b * ((c : ℕ) : ℂ) • E c c =
      (if c = a then ((a : ℕ) : ℂ) • E a b else 0) - (if c = b then ((b : ℕ) : ℂ) • E a b else 0) := by
    intro c
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hE c c a b, smul_sub]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · by_cases h : b = c
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [HH, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_smul]

def adH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ (HH E) - LinearMap.mulRight ℂ (HH E)

theorem adH_apply (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V) :
    adH E T = HH E * T - T * HH E := rfl

theorem adH_mul (E : Fin n → Fin n → Module.End ℂ V) (S T : Module.End ℂ V) :
    adH E (S * T) = adH E S * T + S * adH E T := by
  simp only [adH_apply]; noncomm_ring

theorem HH_NV {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {y : V} (hy : y ∈ NV E) :
    HH E y ∈ NV E := by
  refine Submodule.iSup_induction _ (motive := fun y => HH E y ∈ NV E) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    have h := LinearMap.congr_fun (HH_comm hE i.1.1 i.1.2) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
    rw [sub_eq_iff_eq_add.mp h]
    exact (NV E).add_mem ((NV E).smul_mem _ (mem_NV E i.2 _)) (mem_NV E i.2 _)
  · simp
  · intro x y hx hy
    rw [map_add]; exact (NV E).add_mem hx hy

theorem adH_JJ {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) :
    JJ E ≤ (JJ E).comap (adH E) := by
  intro T hT x
  exact (NV E).sub_mem (HH_NV hE (hT x)) (hT _)

def PP (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ k : ℕ, adH E T = ((k : ℂ) + 1) • T}

theorem congruenceCondition_mul {E : Fin n → Fin n → Module.End ℂ V} {T S : Module.End ℂ V} (hT : T ∈ PP E)
    {m : ℕ} (hS : adH E S = (m : ℂ) • S) : T * S ∈ PP E := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨k, hk⟩ := h
    refine Submodule.subset_span ⟨k + m, ?_⟩
    rw [adH_mul, hk, hS, smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1; push_cast; ring
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact (PP E).add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact (PP E).smul_mem c hx

theorem adH_evd {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (b : FreeAlgebra ℂ (Fin n)) :
    adH E (evd (fun c => E c c) b) = 0 := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, adH_apply, Algebra.commutes, sub_self]
  | grade1 c =>
    simp only [evd, FreeAlgebra.lift_ι_apply, adH_apply, HH_comm hE, sub_self, zero_smul]
  | mul a b ha hb => rw [map_mul, adH_mul, ha, hb]; simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem mem_JJ_of {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {t p : Module.End ℂ V}
    (ht : adH E t = 0) (hp : p ∈ PP E) (h : t - p ∈ JJ E) : t ∈ JJ E := by
  set D : Module.End ℂ (Module.End ℂ V ⧸ JJ E) := (JJ E).mapQ (JJ E) (adH E) (adH_JJ hE) with hD
  have hd := iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep D) 0
  have h1 : (JJ E).mkQ t ∈ D.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, ht]
    rfl
  have h2 : (JJ E).mkQ p ∈ ⨆ j, ⨆ (_ : j ≠ (0 : ℂ)), D.eigenspace j := by
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
  have h3 : (JJ E).mkQ t = (JJ E).mkQ p := (Submodule.Quotient.eq _).mpr h
  rw [← h3] at h2
  have := (Submodule.disjoint_def.mp hd) _ h1 h2
  exact (Submodule.Quotient.mk_eq_zero _).mp this

theorem ev_ι (E : Fin n → Fin n → Module.End ℂ V) (p : Fin n × Fin n) :
    ev E (FreeAlgebra.ι ℂ p) = E p.1 p.2 := by
  simp [ev]

end Mod

inductive Low : FreeAlgebra ℂ (Fin n × Fin n) → Prop
  | one : Low 1
  | mul (u) (p : Fin n × Fin n) : Low u → p.2 ≤ p.1 → Low (u * FreeAlgebra.ι ℂ p)
  | add (u v) : Low u → Low v → Low (u + v)
  | smul (c : ℂ) (u) : Low u → Low (c • u)

theorem Low.zero : Low (0 : FreeAlgebra ℂ (Fin n × Fin n)) := by
  simpa using Low.smul (0 : ℂ) (1 : FreeAlgebra ℂ (Fin n × Fin n)) Low.one

theorem Low.mul' {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∃ b : FreeAlgebra ℂ (Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E u - evd (fun c => E c c) b ∈ PP E := by
  induction hu with
  | one => exact ⟨1, fun V _ _ E _ => by simp⟩
  | mul u p _ hp ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨i, j⟩ := p
    have key : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
        adH E (E i j) = (((i : ℕ) - (j : ℕ) : ℕ) : ℂ) • E i j := by
      intro V _ _ E hE
      rw [adH_apply, HH_comm hE, Nat.cast_sub hp]
    rcases eq_or_lt_of_le hp with h | h
    · simp only at h
      subst h
      refine ⟨b * FreeAlgebra.ι ℂ j, fun V _ _ E hE => ?_⟩
      have := congruenceCondition_mul (hb V E hE) (key V E hE)
      rw [map_mul, map_mul, ev_ι]
      simpa [evd, sub_mul] using this
    · refine ⟨0, fun V _ _ E hE => ?_⟩
      have h1 := congruenceCondition_mul (hb V E hE) (key V E hE)
      have h2 : evd (fun c => E c c) b * E i j ∈ PP E := by
        refine Submodule.subset_span ⟨(i : ℕ) - (j : ℕ) - 1, ?_⟩
        rw [adH_mul, adH_evd hE, key V E hE, zero_mul, zero_add, mul_smul_comm]
        congr 1
        have h' : (j : ℕ) < (i : ℕ) := h
        have : (i : ℕ) - (j : ℕ) = (i : ℕ) - (j : ℕ) - 1 + 1 := by omega
        exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) this
      have h3 := (PP E).add_mem h1 h2
      rw [map_mul, ev_ι, map_zero, sub_zero]
      simpa [sub_mul] using h3
  | add u v _ _ hu hv =>
    obtain ⟨b, hb⟩ := hu
    obtain ⟨b', hb'⟩ := hv
    refine ⟨b + b', fun V _ _ E hE => ?_⟩
    have := (PP E).add_mem (hb V E hE) (hb' V E hE)
    rw [map_add, map_add]
    convert this using 1; abel
  | smul c u _ hu =>
    obtain ⟨b, hb⟩ := hu
    refine ⟨c • b, fun V _ _ E hE => ?_⟩
    rw [map_smul, map_smul, ← smul_sub]
    exact (PP E).smul_mem c (hb V E hE)

def Red (a : FreeAlgebra ℂ (Fin n × Fin n)) : Prop :=
  ∃ u, Low u ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a - ev E u ∈ JJ E

theorem Red.add {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (h' : Red a') : Red (a + a') := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := h'
  refine ⟨u + u', Low.add _ _ hu hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (h V E hE) (h' V E hE)
  rw [map_add, map_add]
  convert this using 1; abel

theorem Red.smul (c : ℂ) {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) : Red (c • a) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨c • u, Low.smul _ _ hu, fun V _ _ E hE => ?_⟩
  rw [map_smul, map_smul, ← smul_sub]
  exact (JJ E).smul_mem c (h V E hE)

theorem Red.of_low {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) : Red u :=
  ⟨u, hu, fun V _ _ E _ => by simp⟩

theorem Red.congr {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a)
    (he : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a' = ev E a) : Red a' := by
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, fun V _ _ E hE => he V E hE ▸ h V E hE⟩

theorem Red.mul_low {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n)
    (hp : p.2 ≤ p.1) : Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨_, Low.mul u p hu hp, fun V _ _ E hE => ?_⟩
  rw [map_mul, map_mul, ← sub_mul]
  exact JJ_mul E (h V E hE) _

theorem Low.red_mul {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∀ p : Fin n × Fin n, Red (u * FreeAlgebra.ι ℂ p) := by
  induction hu with
  | one =>
    intro p
    rcases le_or_gt p.2 p.1 with h | h
    · exact Red.of_low (Low.mul _ p Low.one h)
    · refine ⟨0, Low.zero, fun V _ _ E _ => ?_⟩
      rw [one_mul, map_zero, sub_zero, ev_ι]
      exact fun x => mem_NV E h x
  | mul u y _ hy ih =>
    intro p
    have h1 : Red (if y.2 = p.1 then u * FreeAlgebra.ι ℂ (y.1, p.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    have h2 : Red (if p.2 = y.1 then u * FreeAlgebra.ι ℂ (p.1, y.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    refine ((((ih p).mul_low y hy).add h1).add (h2.smul (-1))).congr fun V _ _ E hE => ?_
    have h := sub_eq_iff_eq_add.mp (hE y.1 y.2 p.1 p.2)
    simp only [map_add, map_mul, ev_ι, map_smul, apply_ite (ev E), map_zero, mul_assoc, h]
    split_ifs <;> simp [mul_add, mul_sub] <;> abel
  | add u v _ _ hu hv => intro p; rw [add_mul]; exact (hu p).add (hv p)
  | smul c u _ hu => intro p; rw [smul_mul_assoc]; exact (hu p).smul c

theorem Red.mul_ι {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n) :
    Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := hu.red_mul p
  refine ⟨u', hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (JJ_mul E (h V E hE) (ev E (FreeAlgebra.ι ℂ p))) (h' V E hE)
  rw [map_mul] at this ⊢
  convert this using 1
  rw [sub_mul]; abel

theorem red_all (a : FreeAlgebra ℂ (Fin n × Fin n)) : Red a := by
  have : ∀ z, Red z → Red (z * a) := by
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro z hz
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact hz.smul r
    | grade1 p => exact fun z hz => hz.mul_ι p
    | mul a b ha hb => intro z hz; rw [← mul_assoc]; exact hb _ (ha _ hz)
    | add a b ha hb => intro z hz; rw [mul_add]; exact (ha _ hz).add (hb _ hz)
  simpa using this 1 (Red.of_low Low.one)

theorem hcdec : CompanionTheory.D.LK.HCdec := by
  intro n a ha
  obtain ⟨u, hu, h⟩ := red_all a
  obtain ⟨b, hb⟩ := hu.mul'
  refine ⟨b, fun V _ _ E hE x => inN_of_mem E ?_⟩
  have h0 : adH E (ev E a - evd (fun c => E c c) b) = 0 := by
    rw [map_sub, adH_evd hE, sub_zero, adH_apply, sub_eq_zero]
    exact (Commute.sum_left _ _ _ fun c _ => (ha V E hE c).smul_left _).eq
  have := mem_JJ_of hE h0 (hb V E hE) (by simpa using h V E hE)
  exact this x

end GlobalTheory.CompanionTheory.HCdecomp
