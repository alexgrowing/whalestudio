import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SecEqProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

variable (ι) in

abbrev Mono (a : K → ℕ) : Type := {μ : (Σ k, ι k) → ℕ // ∀ k, ∑ i, μ ⟨k, i⟩ = a k}

theorem Mono.le {a : K → ℕ} (μ : Mono ι a) (p : Σ k, ι k) : μ.1 p ≤ a p.1 := by
  obtain ⟨k, i⟩ := p
  rw [← μ.2 k]
  exact Finset.single_le_sum (f := fun i => μ.1 ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

instance (a : K → ℕ) : Finite (Mono ι a) :=
  Finite.of_injective
    (fun μ : Mono ι a => fun p => (⟨μ.1 p, Nat.lt_succ_of_le (μ.le p)⟩ : Fin (a p.1 + 1)))
    fun _ _ h => Subtype.ext (funext fun p => congrArg Fin.val (congrFun h p))

def monVal (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : Ω := ∏ p, y p ^ μ p

def monPoly (μ : (Σ k, ι k) → ℕ) : MRing ι := monomial (Finsupp.equivFunOnFinite.symm μ) 1

theorem aeval_monPoly (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : aeval y (monPoly μ) = monVal y μ := by
  rw [monPoly, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem homog_monPoly {a : K → ℕ} (μ : Mono ι a) : IsMultiHomog (monPoly μ.1) a := by
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  simpa using μ.2 k

theorem homog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SectionBounded.homog_one (ι := ι)
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact SectionBounded.homog_mul (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem homog_bind₁ {a : K → ℕ} {N : ℕ} (φ : Fin (N + 1) → MRing ι) (hφ : ∀ j, IsMultiHomog (φ j) a)
    {f : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ} (hf : f.IsHomogeneous n) :
    IsMultiHomog (bind₁ φ f) (fun k => n * a k) := by
  rw [f.as_sum, map_sum]
  refine SectionBounded.homog_sum _ fun m hm => ?_
  rw [bind₁_monomial]
  refine SectionBounded.homog_congr (SectionBounded.homog_mul (SectionBounded.homog_C _)
    (homog_prod _ _ _ fun j _ => SectionBounded.homog_pow (hφ j) (m j))) fun k => ?_
  have hdeg : ∑ j ∈ m.support, m j = n := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [← hdeg, Finset.sum_mul]
  simp [Finset.sum_apply]

variable [DecidableEq K] [∀ k, DecidableEq (ι k)]

def swap (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) : (Σ k, ι k) → ℕ :=
  fun r => μ r + (if p = r then 1 else 0) - (if q = r then 1 else 0)

theorem sum_boole_block (k : K) (i₀ : ι k) (k' : K) :
    ∑ i : ι k', (if (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i⟩ then 1 else 0) = if k = k' then 1 else 0 := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

theorem swap_mem {a : K → ℕ} (μ : Mono ι a) (k : K) (i₀ i : ι k) (h : μ.1 ⟨k, i₀⟩ ≠ 0) (k' : K) :
    ∑ i', swap μ.1 ⟨k, i₀⟩ ⟨k, i⟩ ⟨k', i'⟩ = a k' := by
  unfold swap
  rw [Finset.sum_tsub_distrib, Finset.sum_add_distrib, μ.2 k', sum_boole_block, sum_boole_block,
    Nat.add_sub_cancel]
  intro i' _
  by_cases hq : (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i'⟩
  · cases hq
    rw [if_pos rfl]
    omega
  · rw [if_neg hq]
    exact Nat.zero_le _

theorem monVal_swap (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) (h : μ q ≠ 0) :
    monVal y (swap μ q p) * y q = monVal y μ * y p := by
  have hq : ∏ r, y r ^ (if q = r then 1 else 0) = y q := by simp
  have hp : ∏ r, y r ^ (if p = r then 1 else 0) = y p := by simp
  rw [← hq, ← hp, monVal, monVal, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← pow_add, ← pow_add, swap, Nat.sub_add_cancel]
  by_cases h1 : q = r
  · subst h1
    rw [if_pos rfl]
    omega
  · rw [if_neg h1]
    exact Nat.zero_le _

def pure (c : ∀ k, ι k) (a : K → ℕ) : Mono ι a :=
  ⟨fun r => if c r.1 = r.2 then a r.1 else 0, fun k => by simp⟩

theorem monVal_pure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℕ) :
    monVal y (pure c a).1 = ∏ k, y ⟨k, c k⟩ ^ a k := by
  rw [monVal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pure, pow_ite]

def svPt (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) : Fin (N + 1) → Ω :=
  fun j => monVal y (e.symm j).1

theorem chartLat_le_secs (y : (Σ k, ι k) → Ω) {a : K → ℕ} (ha : ∀ k, 1 ≤ a k) {N : ℕ}
    (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω} (hs : s ∈ chartLat y (fun k => (a k : ℤ)) τ) :
    s ∈ (Kleiman.twistSys ℤ (svPt y e) (τ : ℤ)).secs := by
  rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
  intro I
  obtain ⟨j, hj⟩ := I.2.1
  have hzj : monVal y (e.symm j).1 ≠ 0 := (Kleiman.mem_support (svPt y e)).mp (I.2.2 hj)
  have hex : ∀ k, ∃ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := fun k => by
    have h0 : ∑ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := by rw [(e.symm j).2 k]; exact Nat.one_le_iff_ne_zero.mp (ha k)
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact ⟨i, hi⟩
  choose c hc using hex
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hzj (Finset.prod_eq_zero (Finset.mem_univ ⟨k, c k⟩) (by rw [h0, zero_pow (hc k)]))
  have hle : chartRingZ y c ≤ Kleiman.chartRing ℤ (svPt y e) I := by
    rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine ⟨X (e ⟨swap (e.symm j).1 ⟨k, c k⟩ ⟨k, i⟩, swap_mem (e.symm j) k (c k) i (hc k)⟩), X j, 1,
      Kleiman.X_mem_monos hj, isHomogeneous_X _ _, isHomogeneous_X _ _, ?_⟩
    simp only [aeval_X, svPt, Equiv.symm_apply_apply]
    rw [div_eq_div_iff (hyc k) hzj, monVal_swap y _ _ _ (hc k), mul_comm]
  have hj0 : svPt y e (e (pure c a)) ^ τ ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I :=
    Submodule.subset_span ⟨X (e (pure c a)) ^ τ, 1, 0, τ, one_mem _, isHomogeneous_X_pow _ _,
      isHomogeneous_one _ _, by simp, by simp⟩
  have hmem := Submodule.smul_mem _ (⟨_, hle (hs c hyc)⟩ : Kleiman.chartRing ℤ (svPt y e) I) hj0
  rw [Submodule.restrictScalars_mem]
  change s ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I
  convert hmem using 1
  change s = (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) * _
  rw [svPt, Equiv.symm_apply_apply, monVal_pure, ← Finset.prod_pow, mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one, mul_one]
  intro k _
  rw [← pow_mul, zpow_neg, show (τ : ℤ) * (a k : ℤ) = ((a k * τ : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ (hyc k))]

theorem piece_le_secM (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω}
    (hs : s ∈ (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ)) : s ∈ secM y (fun k => τ * a k) := by
  have hle : (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ) ≤
      Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g (fun k => τ * a k) ∧ aeval y g = s} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, n, hf, hn, rfl⟩
    obtain rfl : n = τ := by exact_mod_cast hn
    refine Submodule.subset_span ⟨bind₁ (fun j => monPoly (e.symm j).1) f,
      homog_bind₁ _ (fun j => homog_monPoly (e.symm j)) hf, ?_⟩
    rw [aeval_bind₁]
    simp only [aeval_monPoly]
    rfl
  exact hle hs

end SecEqProof

open SecEqProof in

theorem SecEq.proof : SecEq.Statement := by
  intro K _ ι _ Ω _ y a ha hy
  classical
  choose c hc using hy
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty (Mono ι a ≃ Fin (N + 1)) := by
    have : Nonempty (Mono ι a) := ⟨pure c a⟩
    exact ⟨Nat.card (Mono ι a) - 1,
      ⟨(Finite.equivFin _).trans (finCongr (Nat.sub_add_cancel Nat.card_pos).symm)⟩⟩
  have hz : svPt y e ≠ 0 := fun h => by
    have h1 := congrFun h (e (pure c a))
    simp only [svPt, Equiv.symm_apply_apply, monVal_pure, Pi.zero_apply] at h1
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hc k)) h1
  obtain ⟨τ₀, hτ₀⟩ := Filter.eventually_atTop.mp (Kleiman.TwistSections.full ℤ Ω N (svPt y e) hz)
  refine ⟨τ₀, fun τ hτ => le_antisymm (fun s hs => ?_)
    (UpperNormalisation.secM_le_chartLat y _ τ fun k => by push_cast; ring)⟩
  exact piece_le_secM y e τ ((hτ₀ τ hτ) ▸ chartLat_le_secs y ha e τ hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
