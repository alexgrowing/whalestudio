import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevCrt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Q : Type} [CommGroup Q]

theorem mulle1 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ I := Ideal.mul_le_inf.trans inf_le_left

theorem mulle2 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ J := Ideal.mul_le_inf.trans inf_le_right

def iSub (D : Datum p) (I : Ideal (𝓞 D.F)) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ I, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

theorem smul_mem_iSub {I : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ I) (z : D.La) :
    algebraMap (𝓞 D.F) D.O c • z ∈ iSub D I :=
  Submodule.subset_span ⟨c, hc, z, rfl⟩

theorem iSub_mono {I J : Ideal (𝓞 D.F)} (h : I ≤ J) : iSub D I ≤ iSub D J :=
  Submodule.span_mono (by rintro _ ⟨c, hc, z, rfl⟩; exact ⟨c, h hc, z, rfl⟩)

theorem smul_mem_iSub_mul {I J : Ideal (𝓞 D.F)} {a : 𝓞 D.F} (ha : a ∈ I) {y : D.La} (hy : y ∈ iSub D J) :
    algebraMap (𝓞 D.F) D.O a • y ∈ iSub D (I * J) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z, rfl⟩ := hx
    rw [smul_smul, ← map_mul]
    exact smul_mem_iSub (Ideal.mul_mem_mul ha hc) z
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [smul_smul, Algebra.commutes, ← smul_smul]
    exact Submodule.smul_mem _ _ hx

theorem mem_iSub_span_nat (n : ℕ) (x : D.La) :
    x ∈ iSub D (Ideal.span {(n : 𝓞 D.F)}) ↔ ∃ y, x = n • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, z, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc
      exact ⟨algebraMap (𝓞 D.F) D.O d • z, by
        rw [map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [smul_add]⟩
    | smul o x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨o • a, by rw [smul_comm]⟩
  · rintro ⟨y, rfl⟩
    have := smul_mem_iSub (D := D) (Ideal.mem_span_singleton_self (n : 𝓞 D.F)) y
    rwa [map_natCast, Nat.cast_smul_eq_nsmul] at this

def IsIdealLev (D : Datum p) (act : D.O → Q → Q) (I : Ideal (𝓞 D.F)) (f : D.La → Q) : Prop :=
  (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ x ∈ iSub D I) ∧
    ∀ g, (∀ c ∈ I, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, f y = g

theorem lev_top (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) : IsIdealLev D act ⊤ (fun _ => 1) := by
  refine ⟨fun _ _ => by simp, fun c _ => ?_, fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
  · exact Eq.symm (by simpa using hm c 1 1)
  · have := smul_mem_iSub (D := D) (I := ⊤) (c := 1) trivial x
    rw [map_one, one_smul] at this
    simpa using this
  · have := hg 1 trivial
    rw [map_one, h1] at this
    exact this.symm

theorem lev_mul (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a) {I J : Ideal (𝓞 D.F)} (hIJ : I ⊔ J = ⊤)
    {f g : D.La → Q} (hf : IsIdealLev D act I f) (hg : IsIdealLev D act J g) :
    IsIdealLev D act (I * J) (fun x => f x * g x) := by
  obtain ⟨fa, fs, fk, fo⟩ := hf
  obtain ⟨ga, gs, gk, go⟩ := hg
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hIJ)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hsplit : ∀ u, act (algebraMap (𝓞 D.F) D.O a) u * act (algebraMap (𝓞 D.F) D.O b) u = u := fun u => by
    rw [← hadd, ← map_add, hab, map_one, h1]
  have fI : ∀ c ∈ I, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (f x) = 1 := fun c hc x => by
    rw [← fs]; exact (fk _).2 (smul_mem_iSub hc x)
  have gJ : ∀ c ∈ J, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (g x) = 1 := fun c hc x => by
    rw [← gs]; exact (gk _).2 (smul_mem_iSub hc x)
  refine ⟨fun x y => ?_, fun c x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun u hu => ?_⟩
  · simp only [fa, ga]; exact mul_mul_mul_comm _ _ _ _
  · simp only [fs, gs, hm]
  · have hx' : f x * g x = 1 := hx
    have e1 : f x = 1 := by
      have h := congrArg (act (algebraMap (𝓞 D.F) D.O b)) hx'
      rw [hm, gJ b hb, _root_.mul_one, hone] at h
      rw [← hsplit (f x), fI a ha, h, _root_.mul_one]
    have e2 : g x = 1 := by rwa [e1, _root_.one_mul] at hx'
    have hxx : x = algebraMap (𝓞 D.F) D.O a • x + algebraMap (𝓞 D.F) D.O b • x := by
      rw [← add_smul, ← map_add, hab, map_one, one_smul]
    rw [hxx]
    refine Submodule.add_mem _ (smul_mem_iSub_mul ha ((gk x).1 e2)) ?_
    rw [_root_.mul_comm I J]
    exact smul_mem_iSub_mul hb ((fk x).1 e1)
  · show f x * g x = 1
    have l1 : I * J ≤ I := mulle1 I J
    have l2 : I * J ≤ J := mulle2 I J
    rw [(fk x).2 (iSub_mono l1 hx), (gk x).2 (iSub_mono l2 hx), _root_.mul_one]
  · have k1 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O c) (act (algebraMap (𝓞 D.F) D.O d) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    have k2 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O d) (act (algebraMap (𝓞 D.F) D.O c) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul, _root_.mul_comm]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    obtain ⟨z, hz⟩ := fo (act (algebraMap (𝓞 D.F) D.O b) u) fun c hc' => k1 c hc' b hb
    obtain ⟨y, hy⟩ := go (act (algebraMap (𝓞 D.F) D.O a) u) fun d hd => k2 a ha d hd
    refine ⟨algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b • z, ?_⟩
    show f _ * g _ = u
    rw [fa, ga, fs, fs, gs, gs, fI a ha, gJ b hb, _root_.one_mul, _root_.mul_one, hz, hy]
    have s1 := hsplit (act (algebraMap (𝓞 D.F) D.O a) u)
    have s2 := hsplit (act (algebraMap (𝓞 D.F) D.O b) u)
    rw [k2 a ha b hb, _root_.mul_one] at s1
    rw [k1 a ha b hb, _root_.one_mul] at s2
    rw [s1, s2, _root_.mul_comm, hsplit]

theorem exists_lev_of_pow_mem (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a)
    (H : ∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l, IsIdealLev D act (w ^ r) l)
    (r : ℕ) (I : Ideal (𝓞 D.F)) : (p : 𝓞 D.F) ^ r ∈ I → ∃ l, IsIdealLev D act I l := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    intro h
    have h0 : (p : 𝓞 D.F) ^ r = 0 := by simpa using h
    exact absurd (pow_eq_zero_iff'.1 h0).1 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  | h1 hu =>
    intro _
    rw [Ideal.isUnit_iff.1 hu]
    exact ⟨_, lev_top act hm h1⟩
  | @hpr q i hq =>
    intro h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact ⟨_, lev_top act hm h1⟩
    · have hp : q.IsPrime := Ideal.isPrime_of_prime hq
      exact H q i (hp.isMaximal hq.ne_zero) (hp.mem_of_pow_mem r (Ideal.pow_le_self hi.ne' h))
  | @hcp x y hxy hx hy =>
    intro h
    obtain ⟨f, hf⟩ := hx (mulle1 x y h)
    obtain ⟨g, hg⟩ := hy (mulle2 x y h)
    have : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact ⟨_, lev_mul act hm h1 hc hadd this hf hg⟩

theorem exists_pLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Q : Type) [CommGroup Q] (act : D.O → Q → Q), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ a, act 1 a = a) → (∀ b c a, act (b * c) a = act b (act c a)) → (∀ b c a, act (b + c) a = act b a * act c a) → (∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l : D.La → Q, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = act c (l x)) ∧ (∀ x, l x = 1 ↔ x ∈ wSub D w r) ∧ ∀ g, (∀ c ∈ w ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g) → ∀ r : ℕ, ∃ f : D.La → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g) := by
  intro p _ D Q _ act hm h1 hc hadd H r
  obtain ⟨f, fa, fs, fk, fo⟩ := exists_lev_of_pow_mem act hm h1 hc hadd H r
    (Ideal.span {((p ^ r : ℕ) : 𝓞 D.F)}) (by
      rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hnat : ∀ (n : ℕ) a, act (n : D.O) a = a ^ n := fun n a => by
    induction n with
    | zero => simpa using hadd 0 0 a
    | succ n ih => rw [Nat.cast_succ, hadd, ih, h1, pow_succ]
  refine ⟨f, fa, fs, fun x => (fk x).trans (mem_iSub_span_nat _ x), fun g => ⟨fun hg => fo g ?_, ?_⟩⟩
  · intro c hc'
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc'
    rw [_root_.mul_comm, map_mul, hc, map_natCast, hnat, hg, hone]
  · rintro ⟨x, rfl⟩
    rw [← hnat, ← fs, Nat.cast_smul_eq_nsmul]
    exact (fk _).2 ((mem_iSub_span_nat _ _).2 ⟨x, rfl⟩)

end GlobalTheory.UPel.HT.EtLev.LevCrt
