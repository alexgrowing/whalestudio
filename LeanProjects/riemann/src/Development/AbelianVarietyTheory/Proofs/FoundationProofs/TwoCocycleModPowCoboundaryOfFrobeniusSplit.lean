import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.FrobCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def J (l : ℕ) [Fact l.Prime] (n : ℕ) : AddSubgroup (Qbar l) where
  carrier := {x | ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖}
  zero_mem' := by simp only [Set.mem_setOf_eq, norm_zero]; exact norm_nonneg _
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := fun ha => by simpa only [Set.mem_setOf_eq, norm_neg] using ha

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ J l n := Iff.rfl

theorem mul_memJ {n : ℕ} {x y : Qbar l} (hy : ‖y‖ ≤ 1) (hx : x ∈ J l n) : y * x ∈ J l n := by
  show ‖y * x‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul hy hx (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))

theorem natMul_memJ (n q : ℕ) {y : Qbar l} (hy : ‖y‖ ≤ 1) : ((l ^ n * q : ℕ) : Qbar l) * y ∈ J l n := by
  show ‖_‖ ≤ _
  rw [norm_mul, Nat.cast_mul, norm_mul, Nat.cast_pow]
  have h1 := IsUltrametricDist.norm_natCast_le_one (Qbar l) q
  calc _ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem eps_mul' (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by
  simp [eps, map_mul]

theorem eps_pow' (s : G ℚ Ω) (i : ℕ) : eps l (s ^ i) = eps l s ^ i := by
  simp [eps, map_pow]

def Tr (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (j : ℕ) : Qbar l :=
  Nat.rec (motive := fun _ => Qbar l) (ξ 1 1) (fun i t => t - ξ (g ^ i) g) j

theorem Tr_zero (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) : Tr ξ g 0 = ξ 1 1 := rfl

theorem Tr_succ (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (j : ℕ) : Tr ξ g (j + 1) = Tr ξ g j - ξ (g ^ j) g := rfl

theorem Tr_mem (c : Coef l) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hint : ∀ s t, ξ s t ∈ c.O) :
    ∀ j, Tr ξ g j ∈ c.O
  | 0 => by rw [Tr_zero]; exact hint 1 1
  | j + 1 => by rw [Tr_succ]; exact sub_mem (Tr_mem c ξ g hint j) (hint _ _)

theorem Tr_key (n : ℕ) (D : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) (i : ℕ) :
    ∀ j, ξ (g ^ i) (g ^ j) - (eps l g ^ i * Tr ξ g j - Tr ξ g (i + j) + Tr ξ g i) ∈ J l n
  | 0 => by
    have h := (cg_iff).1 (hcoc (g ^ i) (pow_mem hg i) 1 D.one_mem 1 D.one_mem)
    simp only [mul_one, eps_pow'] at h
    have e : ξ (g ^ i) (g ^ 0) - (eps l g ^ i * Tr ξ g 0 - Tr ξ g (i + 0) + Tr ξ g i) =
        -(eps l g ^ i * ξ 1 1 + ξ (g ^ i) 1 - (ξ (g ^ i) 1 + ξ (g ^ i) 1)) := by
      simp only [pow_zero, add_zero, Tr_zero]; ring
    rw [e]; exact neg_mem h
  | j + 1 => by
    have ih := Tr_key n D ξ g hg hcoc i j
    have h := (cg_iff).1 (hcoc (g ^ i) (pow_mem hg i) (g ^ j) (pow_mem hg j) g hg)
    rw [eps_pow', ← pow_succ, ← pow_add] at h
    have e : ξ (g ^ i) (g ^ (j + 1)) - (eps l g ^ i * Tr ξ g (j + 1) - Tr ξ g (i + (j + 1)) + Tr ξ g i) =
        (eps l g ^ i * ξ (g ^ j) g + ξ (g ^ i) (g ^ (j + 1)) - (ξ (g ^ (i + j)) g + ξ (g ^ i) (g ^ j))) +
        (ξ (g ^ i) (g ^ j) - (eps l g ^ i * Tr ξ g j - Tr ξ g (i + j) + Tr ξ g i)) := by
      rw [← add_assoc i j 1]; simp only [Tr_succ]; ring
    rw [e]; exact add_mem h ih

theorem Tr_period (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    Tr ξ g (m + j) - (Tr ξ g j + (Tr ξ g m - Tr ξ g 0)) ∈ J l n := by
  have km := Tr_key n D ξ g hg hcoc m j
  have k0 := Tr_key n D ξ g hg hcoc 0 j
  have hi := (cg_iff).1 (hinv 1 D.one_mem (g ^ j) (pow_mem hg j) (g ^ m) hgm).1
  rw [one_mul] at hi
  have he : (eps l g ^ m - 1) ∈ J l n := by
    have := (cg_iff).1 (hepsK _ hgm); rwa [eps_pow'] at this
  have hT := CupCob.norm_le_one_of_mem c (Tr_mem c ξ g hint j)
  have em := mul_memJ hT he
  have e : Tr ξ g (m + j) - (Tr ξ g j + (Tr ξ g m - Tr ξ g 0)) =
      Tr ξ g j * (eps l g ^ m - 1) - (-(ξ (g ^ m) (g ^ j) - (eps l g ^ m * Tr ξ g j - Tr ξ g (m + j) + Tr ξ g m)) +
        (ξ (g ^ m) (g ^ j) - ξ 1 (g ^ j)) +
        (ξ (g ^ 0) (g ^ j) - (eps l g ^ 0 * Tr ξ g j - Tr ξ g (0 + j) + Tr ξ g 0))) := by
    simp only [pow_zero, zero_add]; ring
  rw [e]; exact sub_mem em (add_mem (add_mem (neg_mem km) hi) k0)

theorem Tr_periods (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    ∀ t : ℕ, Tr ξ g (m * t + j) - (Tr ξ g j + (t : Qbar l) * (Tr ξ g m - Tr ξ g 0)) ∈ J l n
  | 0 => by simp only [mul_zero, zero_add, Nat.cast_zero, zero_mul, add_zero, sub_self]; exact zero_mem _
  | t + 1 => by
    have ih := Tr_periods n c D K ξ g hg m hgm hepsK hint hcoc hinv j t
    have hp := Tr_period n c D K ξ g hg m hgm hepsK hint hcoc hinv (m * t + j)
    have e1 : m * (t + 1) + j = m + (m * t + j) := by ring
    rw [e1]
    have e : Tr ξ g (m + (m * t + j)) - (Tr ξ g j + ((t + 1 : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0)) =
        (Tr ξ g (m + (m * t + j)) - (Tr ξ g (m * t + j) + (Tr ξ g m - Tr ξ g 0))) +
        (Tr ξ g (m * t + j) - (Tr ξ g j + (t : Qbar l) * (Tr ξ g m - Tr ξ g 0))) := by
      push_cast; ring
    rw [e]; exact add_mem hp ih

theorem Tr_mod (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    Tr ξ g j - Tr ξ g (j % (m * l ^ n)) ∈ J l n := by
  have h := Tr_periods n c D K ξ g hg m hgm hepsK hint hcoc hinv (j % (m * l ^ n)) (l ^ n * (j / (m * l ^ n)))
  have ej : m * (l ^ n * (j / (m * l ^ n))) + j % (m * l ^ n) = j := by
    rw [← mul_assoc]; exact Nat.div_add_mod j (m * l ^ n)
  rw [ej] at h
  have hd : ‖Tr ξ g m - Tr ξ g 0‖ ≤ 1 :=
    CupCob.norm_le_one_of_mem c (sub_mem (Tr_mem c ξ g hint m) (Tr_mem c ξ g hint 0))
  have h2 := natMul_memJ (l := l) n (j / (m * l ^ n)) hd
  have e : Tr ξ g j - Tr ξ g (j % (m * l ^ n)) =
      (Tr ξ g j - (Tr ξ g (j % (m * l ^ n)) + ((l ^ n * (j / (m * l ^ n)) : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0))) +
      ((l ^ n * (j / (m * l ^ n)) : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0) := by ring
  rw [e]; exact add_mem h h2

theorem isLocallyConstant_hom {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group H] (χ : Γ →* H) (hχ : IsOpen (χ.ker : Set Γ)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set Γ) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem twoCocycleModPow_coboundary_of_frobenius_split (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ)
    (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n)))
    (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (hm : 0 < m) (hφm : ((φ ^ m : ↥D) : G ℚ Ω) ∈ K) (hker : IsOpen (d.ker : Set ↥D))
    (hdec : ∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K)
    (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) :
    Cob2 c n D ξ := by
  classical
  haveI : NeZero (m * l ^ n) := ⟨Nat.mul_ne_zero hm.ne' (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  set g : G ℚ Ω := (φ : G ℚ Ω) with hgdef
  have hg : g ∈ D := φ.2
  have hgm : g ^ m ∈ K := by simpa [hgdef] using hφm
  set k : ↥D → ℕ := fun s => (Multiplicative.toAdd (d s)).val with hkdef
  set T := Tr ξ g with hT
  refine ⟨fun s => if h : s ∈ D then T (k ⟨s, h⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun s : ↥D => T (k s)) :=
      ((isLocallyConstant_hom d hker).comp fun z => T (Multiplicative.toAdd z).val).continuous
    exact hc.congr fun s => by simp [Set.restrict, s.2]
  · intro s; dsimp only; split_ifs
    · exact Tr_mem c ξ g hint _
    · exact zero_mem _
  · intro s hs t ht
    rw [cg_iff]
    set s' : ↥D := ⟨s, hs⟩
    set t' : ↥D := ⟨t, ht⟩
    set a := k s' with ha
    set b := k t' with hb
    have hst : s * t ∈ D := D.mul_mem hs ht
    simp only [dif_pos hs, dif_pos ht, dif_pos hst]
    have hk : k ⟨s * t, hst⟩ = (a + b) % (m * l ^ n) := by
      show (Multiplicative.toAdd (d (s' * t'))).val = _
      rw [map_mul, toAdd_mul, ZMod.val_add]
    rw [hk]
    set κ1 : G ℚ Ω := (((φ ^ a)⁻¹ * s' : ↥D) : G ℚ Ω) with hκ1
    set κ2 : G ℚ Ω := (((φ ^ b)⁻¹ * t' : ↥D) : G ℚ Ω) with hκ2
    have hK1 : κ1 ∈ K := hdec s'
    have hK2 : κ2 ∈ K := hdec t'
    have es : g ^ a * κ1 = s := by simp [hκ1, hgdef, s']
    have et : g ^ b * κ2 = t := by simp [hκ2, hgdef, t']
    have i1 := (cg_iff).1 (hinv (g ^ a) (pow_mem hg a) t ht κ1 hK1).1
    rw [es] at i1
    have i2 := (cg_iff).1 (hinv (g ^ a) (pow_mem hg a) (g ^ b) (pow_mem hg b) κ2 hK2).2
    rw [et] at i2
    have kk := Tr_key n D ξ g hg hcoc a b
    have md := Tr_mod n c D K ξ g hg m hgm hepsK hint hcoc hinv (a + b)
    have he := (cg_iff).1 (hepsK κ1 hK1)
    have hn1 : ‖eps l g ^ a * T b‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (CupCob.norm_le_one_of_mem c (CupCob.eps_mem c g)))
        (norm_nonneg _) (CupCob.norm_le_one_of_mem c (Tr_mem c ξ g hint b))
    have em := mul_memJ hn1 he
    have eeps : eps l s = eps l g ^ a * eps l κ1 := by rw [← es, eps_mul', eps_pow']
    rw [eeps]
    have e : ξ s t - (eps l g ^ a * eps l κ1 * T b - T ((a + b) % (m * l ^ n)) + T a) =
        (ξ s t - ξ (g ^ a) t) + (ξ (g ^ a) t - ξ (g ^ a) (g ^ b)) +
        (ξ (g ^ a) (g ^ b) - (eps l g ^ a * T b - T (a + b) + T a)) -
        eps l g ^ a * T b * (eps l κ1 - 1) - (T (a + b) - T ((a + b) % (m * l ^ n))) := by ring
    rw [e]
    exact sub_mem (sub_mem (add_mem (add_mem i1 i2) kk) em) md

end GlobalTheory.Ord2.FrobCob
