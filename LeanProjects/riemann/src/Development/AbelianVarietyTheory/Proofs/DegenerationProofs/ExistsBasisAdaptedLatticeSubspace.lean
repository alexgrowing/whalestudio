import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

namespace GlobalTheory.TateSeq

variable {M : Type} [AddCommGroup M]

theorem zsmul_congr {N : ℕ} {m : M} (hm : N • m = 0) {a b : ℤ}
    (h : (a : ZMod N) = (b : ZMod N)) : a • m = b • m := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨c, hc⟩ := h
  have : b = a + c * N := by linarith
  rw [this, add_smul, mul_smul, natCast_zsmul, hm, smul_zero, add_zero]

def tors (M : Type) [AddCommGroup M] (N : ℕ) : AddSubgroup M where
  carrier := {x | N • x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [smul_neg, ha, neg_zero]

theorem mem_tors {N : ℕ} {x : M} : x ∈ tors M N ↔ N • x = 0 := Iff.rfl

theorem exists_div (l r : ℕ) [Fact l.Prime]
    (h : ∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (r * n)) (n : ℕ) (y : M)
    (hy : l ^ n • y = 0) : ∃ x : M, l • x = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hc : ∀ n, Nat.card (tors M (l ^ n)) = l ^ (r * n) := h
  let f : tors M (l ^ (n + 1)) →+ tors M (l ^ n) :=
    { toFun := fun x => ⟨l • x.1, by
        rw [mem_tors, ← mul_smul, ← pow_succ]; exact x.2⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hker : Nat.card f.ker = l ^ r := by
    have h1 := hc 1
    rw [mul_one, pow_one] at h1
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          exact congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          have := x.2
          rw [mem_tors] at this
          rw [mem_tors, pow_succ, mul_smul, this, smul_zero]⟩, by
          have := x.2
          rw [mem_tors] at this
          exact Subtype.ext this⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hr : Nat.card f.range = l ^ (r * n) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, hker, hc,
      mul_add, mul_one, pow_add] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hl r) h1).symm
  haveI : Finite (tors M (l ^ n)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [hr, hc])
  have : (⟨y, hy⟩ : tors M (l ^ n)) ∈ f.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x.1, congrArg Subtype.val hx⟩

theorem exists_basis_adapted_lattice_subspace (l r : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc : Nat.card V = l ^ r) :
    ∃ b : Fin r → V,
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : V, ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  letI := Fintype.ofFinite V

  have hdim : Module.finrank (ZMod l) V = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hc] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  let B := Module.finBasisOfFinrankEq (ZMod l) V hdim
  refine ⟨fun i => B i, ?_, ?_⟩
  ·
    intro a ha i
    have h2 : ∑ j, (a j : ZMod l) • B j = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using ha
    have h3 := Fintype.linearIndependent_iff.mp B.linearIndependent _ h2 i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
  ·
    intro y
    refine ⟨fun i => ((B.repr y i).val : ℤ), ?_⟩
    conv_rhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul (ZMod l)]
    simp

theorem exists_basis (l r : ℕ) [Fact l.Prime]
    (h : Nat.card {x : M // l • x = 0} = l ^ r) :
    ∃ b : Fin r → M, (∀ i, l • b i = 0) ∧
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : M, l • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by
  have hc : Nat.card (tors M l) = l ^ r := h
  obtain ⟨b, h1, h2⟩ := @exists_basis_adapted_lattice_subspace l r _ (tors M l) _
    (AddCommGroup.zmodModule (fun x => Subtype.ext x.2)) hc
  refine ⟨fun i => (b i).1, fun i => (b i).2, ?_, ?_⟩
  · intro a ha
    refine h1 a (Subtype.ext ?_)
    simpa using ha
  · intro y hy
    obtain ⟨a, ha⟩ := h2 ⟨y, hy⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩

theorem exists_tower (l : ℕ) (hd : ∀ (n : ℕ) (y : M), l ^ n • y = 0 → ∃ x : M, l • x = y)
    (b : M) (hb : l • b = 0) :
    ∃ e : ℕ → M, e 0 = 0 ∧ e 1 = b ∧ ∀ n, l • e (n + 1) = e n := by
  choose g hg using hd
  let E : (n : ℕ) → {x : M // l ^ (n + 1) • x = 0} := fun n =>
    Nat.rec ⟨b, by simpa using hb⟩
      (fun n x => ⟨g (n + 1) x.1 x.2, by
        rw [pow_succ, mul_smul, hg]; exact x.2⟩) n
  refine ⟨fun n => Nat.casesOn n 0 (fun k => (E k).1), rfl, rfl, ?_⟩
  intro n
  cases n with
  | zero => exact hb
  | succ k => exact hg _ _ _

theorem tower_pow {l : ℕ} {e : ℕ → M} (he : ∀ n, l • e (n + 1) = e n) (k n : ℕ) :
    l ^ k • e (n + k) = e n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ← add_assoc, he, ih]

theorem tower_indep {l r : ℕ} {e : ℕ → Fin r → M} (he : ∀ n i, l • e (n + 1) i = e n i)
    (h1 : ∀ a : Fin r → ℤ, ∑ i, a i • e 1 i = 0 → ∀ i, (l : ℤ) ∣ a i) (n : ℕ) :
    ∀ a : Fin r → ℤ, ∑ i, a i • e n i = 0 → ∀ i, (l : ℤ) ^ n ∣ a i := by
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a ha
    have h2 : ∑ i, a i • e 1 i = 0 := by
      have := congrArg (fun x => l ^ n • x) ha
      simp only [Finset.smul_sum, smul_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, add_comm n 1, tower_pow (e := fun n => e n i) (fun n => he n i)]
    choose c hc using h1 a h2
    have h3 : ∑ i, c i • e n i = 0 := by
      rw [← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_comm, mul_smul, natCast_zsmul, he]
    intro i
    rw [hc, pow_succ']
    exact mul_dvd_mul_left _ (ih c h3 i)

theorem tower_span {l r : ℕ} {e : ℕ → Fin r → M} (he : ∀ n i, l • e (n + 1) i = e n i)
    (h1 : ∀ y : M, l • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • e 1 i = y) (n : ℕ) :
    ∀ y : M, l ^ n • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • e n i = y := by
  induction n with
  | zero => intro y hy; exact ⟨0, by simpa using (by simpa using hy : y = 0).symm⟩
  | succ n ih =>
    intro y hy
    obtain ⟨a, ha⟩ := h1 (l ^ n • y) (by rw [← mul_smul, ← pow_succ']; exact hy)
    obtain ⟨c, hc⟩ := ih (y - ∑ i, a i • e (n + 1) i) (by
      rw [smul_sub, ← ha, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, add_comm n 1, tower_pow (e := fun n => e n i) (fun n => he n i)])
    refine ⟨fun i => a i + c i * l, ?_⟩
    simp only [add_smul, mul_smul, natCast_zsmul, he, Finset.sum_add_distrib, hc]
    abel

end GlobalTheory.TateSeq

namespace GlobalTheory
open TateSeq

theorem exists_tateModule_of_card :
    ∀ (M : Type) [AddCommGroup M] (l r : ℕ) [Fact l.Prime], (∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (r * n)) → ∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℤ_[l] T) (π : ℕ → T →+ M), Module.Free ℤ_[l] T ∧ Module.Finite ℤ_[l] T ∧ Module.finrank ℤ_[l] T = r ∧ (∀ n x, l • π (n + 1) x = π n x) ∧ (∀ x, π 0 x = 0) ∧ (∀ n (a : ℤ_[l]) x, π n (a • x) = (PadicInt.toZModPow n a).val • π n x) ∧ (∀ n y, l ^ n • y = 0 → ∃ x, π n x = y) ∧ (∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y) ∧ ∀ s : ℕ → M, s 0 = 0 → (∀ n, l • s (n + 1) = s n) → ∃! x, ∀ n, π n x = s n := by
  intro M _ l r _ h
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_basis (M := M) l r (by simpa using h 1)
  choose e' he0 he1 he using fun i => exists_tower l (exists_div l r h) (b i) (hb0 i)
  let e : ℕ → Fin r → M := fun n i => e' i n
  have he' : ∀ n i, l • e (n + 1) i = e n i := fun n i => he i n
  have hind := tower_indep he' (by simpa [e, he1] using hb1)
  have hspan := tower_span he' (by simpa [e, he1] using hb2)
  have hkill : ∀ n i, l ^ n • e n i = 0 := fun n i => by
    have := tower_pow (he i) n 0
    rwa [zero_add, he0] at this
  let c : ℕ → ℤ_[l] → ℤ := fun n a => ((PadicInt.toZModPow n a).val : ℤ)
  have hc : ∀ n a, ((c n a : ℤ) : ZMod (l ^ n)) = PadicInt.toZModPow n a := fun n a => by
    simp [c]
  let π : ℕ → (Fin r → ℤ_[l]) →+ M := fun n =>
    { toFun := fun x => ∑ i, c n (x i) • e n i
      map_zero' := by simp [c]
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul]
        apply zsmul_congr (hkill n i)
        push_cast
        simp only [hc, Pi.add_apply, map_add] }
  have hπ : ∀ n (x : Fin r → ℤ_[l]) (a : Fin r → ℤ),
      (∀ i, PadicInt.toZModPow n (x i) = (a i : ZMod (l ^ n))) → π n x = ∑ i, a i • e n i := by
    intro n x a ha
    show ∑ i, c n (x i) • e n i = _
    refine Finset.sum_congr rfl fun i _ => zsmul_congr (hkill n i) ?_
    rw [hc, ha]
  have hker : ∀ n x, π n x = 0 → ∀ i, PadicInt.toZModPow n (x i) = 0 := by
    intro n x hx i
    rw [← hc, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hind n _ hx i
  refine ⟨Fin r → ℤ_[l], inferInstance, inferInstance, π, inferInstance, inferInstance,
    by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    rw [hπ n x (fun i => c (n + 1) (x i))]
    · show l • ∑ i, c (n + 1) (x i) • e (n + 1) i = _
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, he']
    · intro i
      rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n)]
      simp [c]
  · intro x
    show ∑ i, c 0 (x i) • e 0 i = 0
    simp [e, he0]
  · intro n a x
    rw [hπ n (a • x) (fun i => c n a * c n (x i))]
    · show _ = _ • ∑ i, c n (x i) • e n i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
      simp only [c, natCast_zsmul]
    · intro i
      push_cast
      simp [hc]
  · intro n y hy
    obtain ⟨a, ha⟩ := hspan n y hy
    exact ⟨fun i => (a i : ℤ_[l]), by rw [hπ n _ a (fun i => by simp), ha]⟩
  · intro n x
    constructor
    · intro hx
      have : ∀ i, ∃ y : ℤ_[l], y * (l : ℤ_[l]) ^ n = x i := fun i => by
        have h1 : x i ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hker n x hx i
        rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h1
      choose y hy using this
      refine ⟨y, funext fun i => ?_⟩
      simp [← hy, mul_comm]
    · rintro ⟨y, rfl⟩
      rw [map_nsmul]
      show l ^ n • ∑ i, c n (y i) • e n i = 0
      rw [Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, hkill, smul_zero]
  · intro s hs0 hs
    have hsk : ∀ n, l ^ n • s n = 0 := fun n => by
      have := tower_pow hs n 0
      rwa [zero_add, hs0] at this
    choose a ha using fun n => hspan n (s n) (hsk n)
    have hdv : ∀ i n, (l : ℤ) ^ n ∣ a (n + 1) i - a n i := by
      intro i n
      refine hind n (fun i => a (n + 1) i - a n i) ?_ i
      simp only [sub_smul, Finset.sum_sub_distrib, ha]
      rw [sub_eq_zero, ← hs n, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, he']
    refine ⟨fun i => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => a n i) l (hdv i)), ?_, ?_⟩
    · intro n
      rw [hπ n _ (a n) (fun i =>
        PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) l (hdv i) n), ha]
    · intro y hy
      funext i
      rw [← PadicInt.ext_of_toZModPow]
      intro n
      rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => a n i) l (hdv i) n,
        ← hc, ZMod.intCast_eq_intCast_iff_dvd_sub]
      push_cast
      refine hind n (fun i => a n i - c n (y i)) ?_ i
      simp only [sub_smul, Finset.sum_sub_distrib, ha]
      rw [sub_eq_zero, ← hy n]
      rfl

end GlobalTheory
