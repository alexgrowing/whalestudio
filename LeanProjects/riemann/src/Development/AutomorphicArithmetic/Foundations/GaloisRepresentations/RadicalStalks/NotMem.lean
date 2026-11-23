import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.ParL

variable {C : Type} [CommRing C] [IsDedekindDomain C]

private lemma cop {w J : Ideal C} (hw : w.IsMaximal) (h : ¬ w ∣ J) : IsCoprime w J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  apply h
  rw [Ideal.dvd_iff_le]
  have hle : w ≤ w ⊔ J := le_sup_left
  have heq : w = w ⊔ J := hw.eq_of_le hne hle
  rw [heq]
  exact le_sup_right

private lemma notMem {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a y : C}
    (ha : Ideal.span {a} = w * B) (hB : ¬ w ∣ B) (hy : y ∉ w) (m : ℕ)
    (h : y * a ^ m ∈ w ^ (m + 1)) : False := by
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have h1 : w ^ (m + 1) ∣ Ideal.span {y * a ^ m} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ha, mul_pow,
    pow_succ, show Ideal.span {y} * (w ^ m * B ^ m) = w ^ m * (Ideal.span {y} * B ^ m) by ring] at h1
  have hw0' : w ^ m ≠ 0 := pow_ne_zero _ hw0
  rw [mul_dvd_mul_iff_left hw0'] at h1
  rcases hwp.dvd_or_dvd h1 with h2 | h2
  · apply hy
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  · exact hB (hwp.dvd_of_dvd_pow h2)

private lemma approx {w B : Ideal C} {a : C} (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m k : ℕ) {x : C} (hx : x ∈ w ^ m) : ∃ u, x - a ^ m * u ∈ w ^ (m + k) := by
  have hc' : IsCoprime (B ^ m) (w ^ k) := (hc.symm.pow_left).pow_right
  have htop : B ^ m ⊔ w ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hc'
  have hx' : x ∈ Ideal.span {a} ^ m ⊔ w ^ (m + k) := by
    rw [ha, mul_pow, pow_add, ← Ideal.mul_sup, htop, Ideal.mul_top]
    exact hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, rfl⟩ := hy
  refine ⟨u, ?_⟩
  have : x - a ^ m * u = z := by rw [← hyz]; ring
  rw [this]
  exact hz

private lemma divA {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a : C}
    (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m : ℕ) {x : C} (hx : a * x ∈ w ^ (m + 1)) : x ∈ w ^ m := by
  have h1 : w ^ (m + 1) ∣ Ideal.span {a * x} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hx
  rw [← Ideal.span_singleton_mul_span_singleton, ha, pow_succ', _root_.mul_assoc,
    mul_dvd_mul_iff_left hw0] at h1
  have h2 : w ^ m ∣ Ideal.span {x} := (hc.pow_left).dvd_of_dvd_mul_left h1
  rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2

set_option maxHeartbeats 200000 in

private lemma exPar (p : ℕ) (hp0 : (p : C) ≠ 0) {w : Ideal C} (hw : w.IsMaximal)
    (hpw : (p : C) ∈ w) (f : ℕ) (hf : 0 < f) : Nonempty (Par p w f) := by
  have hw0 : w ≠ ⊥ := by
    intro h0
    apply hp0
    rw [h0] at hpw
    exact (Submodule.mem_bot C).mp hpw
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have hP0 : Ideal.span {(p : C)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  obtain ⟨m, B, hwB, hPB⟩ := WfDvdMonoid.max_power_factor' hP0 hwp.not_unit
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · exfalso
      apply hwB
      rw [pow_zero, _root_.one_mul] at hPB
      rw [← hPB, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hpw
    · exact ⟨n, rfl⟩
  have hcB : IsCoprime w B := cop hw hwB
  have hmemP : ∀ z, z ∈ w ^ (n + 1) → z ∈ B → (p : C) ∣ z := by
    intro z hz1 hz2
    rw [← Ideal.mem_span_singleton, hPB,
      Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp hcB.pow_left)]
    exact Ideal.mem_inf.mpr ⟨hz1, hz2⟩
  have hPle : ∀ z, (p : C) ∣ z → z ∈ w ^ (n + 1) := by
    intro z hz
    have hz' : z ∈ w ^ (n + 1) * B := by
      rw [← hPB]
      exact Ideal.mem_span_singleton.mpr hz
    have hle : w ^ (n + 1) * B ≤ w ^ (n + 1) := Ideal.mul_le_left
    exact hle hz'
  have hcM : IsCoprime (w ^ ((n + 1) * f)) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ ((n + 1) * f) ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcM]
      exact Submodule.mem_top)
  have hεB : j ∈ B := Ideal.pow_le_self hf.ne' hj
  have hi' : i ∈ w ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right _ hf) hi
  have h1ε : 1 - j = i := by
    rw [← hij]
    ring
  have hj1 : j - 1 ∈ w ^ (n + 1) := by
    have e : j - 1 = -i := by
      rw [← h1ε]
      ring
    rw [e]
    exact neg_mem hi'
  have hεw : j - 1 ∈ w := Ideal.pow_le_self (Nat.succ_ne_zero n) hj1
  have hεnot : j ∉ w := by
    intro h
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : j - (j - 1) ∈ w := w.sub_mem h hεw
    rwa [sub_sub_cancel] at h2
  have hnle : ¬ w ≤ w ^ 2 := by
    intro hle
    have h1 : w * w ∣ w * 1 := by
      rw [_root_.mul_one, ← pow_two]
      exact Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_left hw0] at h1
    have h2 := Ideal.dvd_iff_le.mp h1
    rw [Ideal.one_eq_top, top_le_iff] at h2
    exact hw.ne_top h2
  obtain ⟨t, ht, ht2⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc2 : IsCoprime (w ^ 2) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i2, hi2, j2, hj2, hij2⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ 2 ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hc2]
      exact Submodule.mem_top)
  obtain ⟨a, haw, haB, ha2⟩ : ∃ a, a ∈ w ∧ a ∈ B ^ f ∧ a ∉ w ^ 2 := by
    refine ⟨t * j2, w.mul_mem_right _ ht, Ideal.mul_mem_left _ _ hj2, ?_⟩
    intro h
    apply ht2
    have e : t = t * j2 + t * i2 := by
      rw [← mul_add, add_comm, hij2, _root_.mul_one]
    rw [e]
    exact (w ^ 2).add_mem h (Ideal.mul_mem_left _ _ hi2)
  have haBB : a ∈ B := Ideal.pow_le_self hf.ne' haB
  obtain ⟨B', hB'⟩ : w ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haw)
  have hwB' : ¬ w ∣ B' := by
    intro hd
    apply ha2
    have h2 : w ^ 2 ∣ Ideal.span {a} := by
      rw [hB', pow_two]
      exact mul_dvd_mul_left w hd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  have hcB' : IsCoprime w B' := cop hw hwB'
  have hs : (p : C) ^ f ∣ a * (1 - j) := by
    have h3 : (1 - j) * a ∈ w ^ ((n + 1) * f) * B ^ f := by
      refine Ideal.mul_mem_mul ?_ haB
      rw [h1ε]
      exact hi
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hPB, mul_pow, ← pow_mul,
      _root_.mul_comm a]
    exact h3
  obtain ⟨s, hs'⟩ := hs
  have hprod : (p : C) ∣ a * (j * a ^ n) := by
    apply hmemP
    · have e : a * (j * a ^ n) = j * a ^ (n + 1) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haw _)
    · exact Ideal.mul_mem_right _ _ haBB
  obtain ⟨c, hc⟩ := hprod
  have hcw : c ∉ w := by
    intro hcw
    apply notMem hw hw0 hB' hwB' hεnot (n + 1)
    have e : j * a ^ (n + 1) = (p : C) * c := by
      rw [← hc]
      ring
    rw [e, pow_succ]
    exact Ideal.mul_mem_mul (hPle _ dvd_rfl) hcw
  have hcc : IsCoprime (w ^ (n + 1)) (Ideal.span {c}) := by
    refine IsCoprime.pow_left (cop hw ?_)
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  obtain ⟨i3, hi3, j3, hj3, hij3⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ (n + 1) ⊔ Ideal.span {c} by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcc]
      exact Submodule.mem_top)
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hj3
  have hinv : (p : C) ∣ c' * c * j - j := by
    have e1 : c' * c = 1 - i3 := by
      rw [← hij3]
      ring
    have e : c' * c * j - j = -(i3 * j) := by
      rw [e1]
      ring
    rw [e]
    exact hmemP _ (neg_mem (Ideal.mul_mem_right _ _ hi3)) (neg_mem (Ideal.mul_mem_left _ _ hεB))
  have hidem : (p : C) ∣ j * j - j := by
    have e : j * j - j = (j - 1) * j := by ring
    rw [e]
    exact hmemP _ (Ideal.mul_mem_right _ _ hj1) (Ideal.mul_mem_left _ _ hεB)
  have hoff : ∀ (w' : Ideal C), w'.IsMaximal → (p : C) ∈ w' → w' ≠ w → j ∈ w' := by
    intro w' hw' hpw' hne
    have hle : w ^ (n + 1) * B ≤ w' := by
      rw [← hPB]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hpw'
    rcases hw'.isPrime.mul_le.mp hle with h | h
    · exact absurd (hw.eq_of_le hw'.ne_top (hw'.isPrime.le_of_pow_le h)).symm hne
    · exact h hεB
  have hgeps : (p : C) ∣ j * (j * a ^ n) - j * a ^ n := by
    have e : j * (j * a ^ n) - j * a ^ n = (j * j - j) * a ^ n := by ring
    rw [e]
    exact dvd_mul_of_dvd_left hidem _
  have hnil : ∃ e, (p : C) ∣ a ^ e * j :=
    ⟨n + 1, hmemP _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow haw _))
      (Ideal.mul_mem_left _ _ hεB)⟩
  have hgen : ∀ x ∈ w, ∃ u, (p : C) ∣ j * x - a * u := by
    intro x hx
    obtain ⟨u, hu⟩ := approx hB' hcB' 1 n (by rwa [pow_one])
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - a * u = (j - 1) * x + (x - a ^ 1 * u) := by ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hj1) ?_
      rwa [add_comm 1 n] at hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB) (Ideal.mul_mem_right _ _ haBB)
  have hannA : ∀ (x : C), (p : C) ∣ a * x → ∃ u, (p : C) ∣ j * x - j * a ^ n * u := by
    intro x hx
    have hx2 : x ∈ w ^ n := divA hw hw0 hB' hcB' n (hPle _ hx)
    obtain ⟨u, hu⟩ := approx hB' hcB' n 1 hx2
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - j * a ^ n * u = j * (x - a ^ n * u) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hεB))
  have hannG : ∀ (x : C), (p : C) ∣ j * a ^ n * x →
      ∃ u v, (p : C) ∣ x - a * u - (1 - j) * v := by
    intro x hx
    have hxw : x ∈ w := by
      by_contra hxw
      have hy : j * x ∉ w := fun h => (hw.isPrime.mem_or_mem h).elim hεnot hxw
      apply notMem hw hw0 hB' hwB' hy n
      have e : j * x * a ^ n = j * a ^ n * x := by ring
      rw [e]
      exact hPle _ hx
    obtain ⟨u, hu⟩ := hgen x hxw
    refine ⟨u, x, ?_⟩
    have e : x - a * u - (1 - j) * x = j * x - a * u := by ring
    rw [e]
    exact hu
  exact ⟨Par.mk j a (j * a ^ n) c c' s hidem hεw hoff haw hs' hc hinv hgeps hnil hgen
    hannG hannA⟩

end UpperTheory.Gal.Ord.ParL

theorem UpperTheory.Gal.Ord.par :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (w : Ideal (𝓞 F)) (f : ℕ), w.IsMaximal → (p : 𝓞 F) ∈ w → 0 < f → Nonempty (Par p w f) := by
  intro p _ F _ _ w f hw hpw hf
  exact UpperTheory.Gal.Ord.ParL.exPar p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hw hpw f hf
