import Formalism.GaussJetBounds.GenLogInverse
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

namespace ExponentialDerivativeInverse

section Sub

variable {K : Type u} [NormedField K] {ι : Type v} {K0 : Subfield K}

def InSub (K0 : Subfield K) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ K0

theorem inSub_add {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f + g) := fun n => by rw [map_add]; exact K0.add_mem (hf n) (hg n)

theorem inSub_sub {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f - g) := fun n => by rw [map_sub]; exact K0.sub_mem (hf n) (hg n)

theorem inSub_zero : InSub K0 (0 : MvPowerSeries ι K) := fun n => by
  rw [map_zero]; exact K0.zero_mem

theorem inSub_one : InSub K0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_X (x : ι) : InSub K0 (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact K0.one_mem
  · exact K0.zero_mem

theorem inSub_mul {f g : MvPowerSeries ι K} (hf : InSub K0 f) (hg : InSub K0 g) :
    InSub K0 (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact K0.sum_mem fun p _ => K0.mul_mem (hf p.1) (hg p.2)

theorem inSub_pow {f : MvPowerSeries ι K} (hf : InSub K0 f) (k : ℕ) : InSub K0 (f ^ k) := by
  induction k with
  | zero => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact inSub_mul ih hf

theorem inSub_prod {α : Type w} (s : Finset α) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, InSub K0 (F i)) : InSub K0 (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inSub_one : InSub K0 (1 : MvPowerSeries ι K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact inSub_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem finsum_mem_sub {α : Type w} (g : α → K) (h : ∀ i, g i ∈ K0) : ∑ᶠ i, g i ∈ K0 := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact K0.sum_mem fun i _ => h i
  · rw [finsum_of_infinite_support hfin]
    exact K0.zero_mem

theorem inSub_subst {σ : Type w} [Finite σ] {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, InSub K0 (a s))
    {f : MvPowerSeries σ K} (hf : InSub K0 f) : InSub K0 (MvPowerSeries.subst a f) := by
  intro n
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_mem_sub _ fun m => ?_
  rw [smul_eq_mul]
  exact K0.mul_mem (hf m) (inSub_prod m.support _ (fun s _ => inSub_pow (ha s) _) n)

theorem inSub_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : InSub K0 D) : InSub K0 (mvExp D) := by
  intro n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)]
  refine finsum_mem_sub _ fun k => ?_
  rw [smul_eq_mul, PowerSeries.coeff_exp]
  have hq : algebraMap ℚ K (1 / (k.factorial : ℚ)) ∈ K0 := by
    rw [map_div₀, map_one, map_natCast]
    exact K0.div_mem K0.one_mem (natCast_mem K0 _)
  exact K0.mul_mem hq (inSub_pow hD k n)

end Sub

section Wt

variable {K : Type u} [NormedField K] {ι : Type v}

def wsum (w : ι → ℤ) (n : ι →₀ ℕ) : ℤ := n.sum fun x k => (k : ℤ) * w x

theorem wsum_add (w : ι → ℤ) (m n : ι →₀ ℕ) : wsum w (m + n) = wsum w m + wsum w n := by
  classical
  unfold wsum
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)

theorem wsum_zero (w : ι → ℤ) : wsum w (0 : ι →₀ ℕ) = 0 := by simp [wsum]

theorem wsum_single (w : ι → ℤ) (x : ι) (k : ℕ) : wsum w (Finsupp.single x k) = k * w x := by
  simp [wsum]

def HomW (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → wsum w n = c

def CongW (N : ℤ) (w : ι → ℤ) (f : MvPowerSeries ι K) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ≠ 0 → N ∣ wsum w n

theorem exists_ne_zero_of_finsum_ne_zero {α : Type w} {g : α → K} (h : ∑ᶠ i, g i ≠ 0) :
    ∃ i, g i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (finsum_eq_zero_of_forall_eq_zero hc)

variable {w : ι → ℤ}

theorem homW_X (x : ι) : HomW w (w x) (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_X] at hn
  split_ifs at hn with h
  · rw [h, wsum_single]; simp
  · exact absurd rfl hn

theorem homW_zero (c : ℤ) : HomW w c (0 : MvPowerSeries ι K) := by
  intro n hn; simp at hn

theorem homW_one : HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_one] at hn
  split_ifs at hn with h
  · rw [h, wsum_zero]
  · exact absurd rfl hn

theorem homW_add {c : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c g) :
    HomW w c (f + g) := by
  intro n hn
  rw [map_add] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_add] at hn; exact hg n hn
  · exact hf n h

theorem homW_mul {c c' : ℤ} {f g : MvPowerSeries ι K} (hf : HomW w c f) (hg : HomW w c' g) :
    HomW w (c + c') (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add, hf p.1 (left_ne_zero_of_mul hpn), hg p.2 (right_ne_zero_of_mul hpn)]

theorem homW_pow {c : ℤ} {f : MvPowerSeries ι K} (hf : HomW w c f) (k : ℕ) :
    HomW w (k * c) (f ^ k) := by
  induction k with
  | zero => intro n hn; simpa using homW_one n (by simpa using hn)
  | succ k ih =>
    rw [pow_succ]
    intro n hn
    rw [homW_mul ih hf n hn]
    push_cast; ring

theorem homW_prod {α : Type w} (s : Finset α) (c : α → ℤ) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, HomW w (c i) (F i)) : HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  first | exact UpperTheory.Reformulated.B.Qi22.homW_prod .. | (apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F h | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K

variable {N : ℤ}

theorem congW_sub {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · rw [h, zero_sub, neg_ne_zero] at hn; exact hg n hn
  · exact hf n h

theorem congW_one : CongW N w (1 : MvPowerSeries ι K) := by
  intro n hn
  rw [homW_one n hn]
  exact dvd_zero N

theorem congW_mul {f g : MvPowerSeries ι K} (hf : CongW N w f) (hg : CongW N w g) :
    CongW N w (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, wsum_add]
  exact dvd_add (hf p.1 (left_ne_zero_of_mul hpn)) (hg p.2 (right_ne_zero_of_mul hpn))

theorem congW_pow {f : MvPowerSeries ι K} (hf : CongW N w f) (k : ℕ) : CongW N w (f ^ k) := by
  induction k with
  | zero => simpa using (congW_one : CongW N w (1 : MvPowerSeries ι K))
  | succ k ih => rw [pow_succ]; exact congW_mul ih hf

theorem congW_subst {σ : Type w} [Finite σ] {w1 : σ → ℤ} {a : σ → MvPowerSeries ι K}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, HomW w (w1 s) (a s))
    {f : MvPowerSeries σ K} (hf : CongW N w1 f) : CongW N w (MvPowerSeries.subst a f) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)] at hn
  obtain ⟨m, hm⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hm
  have h1 := hf m (left_ne_zero_of_mul hm)
  have h2 := homW_prod m.support (fun s => (m s : ℤ) * w1 s) (fun s => a s ^ m s)
    (fun s _ => homW_pow (ha s) (m s)) n (right_ne_zero_of_mul hm)
  rw [h2]
  exact h1

theorem congW_mvExp [CharZero K] {D : MvPowerSeries ι K}
    (hD0 : MvPowerSeries.constantCoeff D = 0) (hD : CongW N w D) : CongW N w (mvExp D) := by
  intro n hn
  unfold mvExp at hn
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hD0)] at hn
  obtain ⟨k, hk⟩ := exists_ne_zero_of_finsum_ne_zero hn
  simp only [smul_eq_mul] at hk
  exact congW_pow hD k n (right_ne_zero_of_mul hk)

theorem zpow_sum_of_ne {α : Type w} (s : Finset α) {ζ : K} (hζ : ζ ≠ 0) (f : α → ℤ) :
    ζ ^ (∑ i ∈ s, f i) = ∏ i ∈ s, ζ ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hζ, ih]

end Wt

section Torus

variable {K : Type u} [NormedField K] {d : ℕ}

theorem congW_of_torus {l : ℕ} [NeZero d] {ζ : K} (hN : l ^ d - 1 ≠ 0)
    (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) {be : MvPowerSeries (ZMod d) K}
    (hbe : MvPowerSeries.subst (torus l ζ) be = be) :
    CongW ((l ^ d - 1 : ℕ) : ℤ) (lw l) be := by
  classical
  intro n hn
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have ht : torus (d := d) l ζ = (fun s : ZMod d => ζ ^ lw l s) • (MvPowerSeries.X : ZMod d → MvPowerSeries (ZMod d) K) := by
    funext s
    simp [torus, MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst] at hbe
  have hc := congrArg (MvPowerSeries.coeff n) hbe
  rw [MvPowerSeries.coeff_rescale] at hc
  have hprod : (n.prod fun s m => (ζ ^ lw l s) ^ m) = ζ ^ wsum (lw l) n := by
    unfold wsum Finsupp.prod Finsupp.sum
    rw [zpow_sum_of_ne _ hζ0]
    refine Finset.prod_congr rfl fun s _ => ?_
    beta_reduce
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hprod] at hc
  have hu : ζ ^ wsum (lw l) n = 1 := by
    have h2 : (ζ ^ wsum (lw l) n - 1) * MvPowerSeries.coeff n be = 0 := by
      rw [sub_mul, hc, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn
  exact (hζ.zpow_eq_one_iff_dvd _).mp hu

end Torus

section Diff

variable {K : Type u} [NormedField K] {d : ℕ}

def Good (K0 : Subfield K) (N : ℤ) (w : V2 d → ℤ) (f : MvPowerSeries (V2 d) K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ InSub K0 f ∧ CongW N w f

theorem good_sub {K0 : Subfield K} {N : ℤ} {w : V2 d → ℤ} {f g : MvPowerSeries (V2 d) K}
    (hf : Good K0 N w f) (hg : Good K0 N w g) : Good K0 N w (f - g) :=
  ⟨by rw [map_sub, hf.1, hg.1, sub_zero], inSub_sub hf.2.1 hg.2.1, congW_sub hf.2.2 hg.2.2⟩

def Fam (K0 : Subfield K) (l : ℕ) (a : ZMod d → MvPowerSeries (V2 d) K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (a s) = 0 ∧ InSub K0 (a s) ∧
    HomW (fun x : V2 d => lw l x.2) (lw l s) (a s)

theorem good_subst [NeZero d] {K0 : Subfield K} {l : ℕ} {N : ℤ} {be : MvPowerSeries (ZMod d) K}
    (hK0 : InSub K0 be) (hcc : MvPowerSeries.constantCoeff be = 0) (hcb : CongW N (lw l) be)
    {a : ZMod d → MvPowerSeries (V2 d) K} (ha : Fam K0 l a) :
    Good K0 N (fun x : V2 d => lw l x.2) (MvPowerSeries.subst a be) :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1) (fun s => (ha s).1) hcc,
    inSub_subst (fun s => (ha s).1) (fun s => (ha s).2.1) hK0,
    congW_subst (fun s => (ha s).1) (fun s => (ha s).2.2) hcb⟩

variable {K0 : Subfield K} {l : ℕ}

theorem zero_series_family : Fam K0 l (s0 (K := K) (d := d)) := fun s =>
  ⟨by simp [s0], inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_alt_series_family : Fam K0 l (s1 (K := K) (d := d)) := by
  intro s
  unfold s1
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩

theorem swappedParity_series_family : Fam K0 l (s2 (K := K) (d := d)) := by
  intro s
  unfold s2
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩

theorem oddIndicator_series_family : Fam K0 l (s1' (K := K) (d := d)) := by
  intro s
  unfold s1'
  split_ifs
  · exact ⟨by simp, inSub_add (inSub_X _) inSub_zero,
      homW_add (homW_X (false, s)) (homW_zero _)⟩
  · exact ⟨by simp, inSub_add (inSub_X _) (inSub_X _),
      homW_add (homW_X (false, s)) (homW_X (true, s))⟩

theorem parityIndicator_series_family : Fam K0 l (s2' (K := K) (d := d)) := by
  intro s
  unfold s2'
  split_ifs
  · exact ⟨by simp, inSub_X _, homW_X (false, s)⟩
  · exact ⟨by simp, inSub_X _, homW_X (true, s)⟩

end Diff

end ExponentialDerivativeInverse

open ExponentialDerivativeInverse in

theorem exponential_derivative_inverse : ExpDeInv.{u} := by
  intro K _ _ l d _ hl hd _ K0 ζ hζ be hK0 htor hcc D hD
  have hN : l ^ d - 1 ≠ 0 := by
    have h2 : 2 ≤ l ^ d := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    omega
  have hcb := congW_of_torus hN hζ htor
  have hD' : Good K0 ((l ^ d - 1 : ℕ) : ℤ) (fun x : V2 d => lw l x.2) D := by
    rcases hD with rfl | rfl
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_alt_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb swappedParity_series_family)
    · exact good_sub (good_sub (good_subst hK0 hcc hcb oddIndicator_series_family) (good_subst hK0 hcc hcb zero_series_family))
        (good_subst hK0 hcc hcb parityIndicator_series_family)
  exact ⟨inSub_mvExp hD'.1 hD'.2.1, fun n hn => congW_mvExp hD'.1 hD'.2.2 n hn⟩

end Formalism.DworkPowerSeriesWeights
