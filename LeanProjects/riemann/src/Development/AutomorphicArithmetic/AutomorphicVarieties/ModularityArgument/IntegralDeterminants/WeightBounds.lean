import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.EigAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.OpBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.RootBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.ProdNorm

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section Nu

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem nu_mul' (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu, map_mul, norm_mul]

private theorem nu_pow' (x : ℂ) (k : ℕ) : nu ι (x ^ k) = nu ι x ^ k := by
  simp [nu, map_pow, norm_pow]

private theorem nu_zero' : nu ι 0 = 0 := by
  simp [nu]

private theorem nu_nonneg' (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private theorem roots_le {q : ℂ} (hq : nu ι q ≤ 1) {c : ℝ} (hc : 0 ≤ c) (S : Multiset ℂ)
    (h : ∀ j, 1 ≤ j → j ≤ S.card → ∃ a : ℂ, q ^ j.choose 2 * a = S.esymm j ∧ nu ι a ≤ c ^ j) :
    ∀ b ∈ S, nu ι b ≤ c := by
  refine rootBound l ι S c hc fun j h1 h2 => ?_
  obtain ⟨a, ha, hb⟩ := h j h1 h2
  rw [← ha, nu_mul', nu_pow']
  calc nu ι q ^ j.choose 2 * nu ι a ≤ 1 * nu ι a :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg' ι q) hq) (nu_nonneg' ι a)
    _ ≤ c ^ j := by rwa [one_mul]

end Nu

private theorem weight_bounds {n : ℕ} (hn : 1 ≤ n) (lam : DomWeight n) {lo hi : ℤ}
    (h : Within n (infOfWeight lam) lo hi) (i : Fin n) :
    lo + ((n : ℤ) - 1) ≤ lam.w i ∧ lam.w i ≤ hi := by
  have key : ∀ k : Fin n, lo + ((k : ℕ) : ℤ) ≤ lam.w k ∧ lam.w k ≤ hi + ((k : ℕ) : ℤ) := by
    intro k
    obtain ⟨m, hm, h1, h2⟩ := h ((lam.w k : ℂ) + (((n : ℂ) - 1) / 2 - (k : ℕ)))
      (Multiset.mem_map.2 ⟨k, Finset.mem_univ_val k, rfl⟩)
    have e1 : ((lam.w k - ((k : ℕ) : ℤ) : ℤ) : ℂ) = (m : ℂ) := by
      push_cast
      linear_combination hm
    have e2 : lam.w k - ((k : ℕ) : ℤ) = m := by exact_mod_cast e1
    omega
  have h0 := (key ⟨0, by omega⟩).2
  have h1 := (key ⟨n - 1, by omega⟩).1
  have a0 : lam.w i ≤ lam.w ⟨0, by omega⟩ := lam.anti (Fin.mk_le_of_le_val (Nat.zero_le _))
  have a1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w i := lam.anti (Fin.le_def.2 (by simp; omega))
  simp only at h0 h1
  omega

private theorem algSat_as_map (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sq_factor (N n : ℕ) (hn : 1 ≤ n) :
    ((((N : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ 2 = (N : ℂ) ^ (n - 1) := by
  have h : ((N : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ 2 = (N : ℝ) ^ (n - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N), ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub hn]
    push_cast
    ring
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h

theorem coreU : CoreU := by
  intro l _ ι E _ _ _ n hn σ hσ lam hlam w hw τ B hc hB lo hi hW b hb
  obtain ⟨hun, hcard, hE⟩ := eigAll E n σ hσ w hw τ B hc hB
  obtain ⟨hv, hprod⟩ := prodNorm l ι E w
  have hvne : ∀ t ∈ Ov ι w, nu ι (t (unif w : E)) ≠ 0 := fun t ht => (hv t ht).1.ne'
  have hq1 : nu ι (normV w : ℂ) ≤ 1 := by
    rw [← hprod]
    exact Finset.prod_le_one (fun t ht => (hv t ht).1.le) fun t ht => (hv t ht).2.le
  have hq0 : 0 < nu ι (normV w : ℂ) := by
    rw [← hprod]
    exact Finset.prod_pos fun t ht => (hv t ht).1
  have hqne : (normV w : ℂ) ≠ 0 := by
    intro h0
    rw [h0, nu_zero'] at hq0
    exact lt_irrefl _ hq0
  have hlh : ∀ t i, lo t + ((n : ℤ) - 1) ≤ (lam t).w i ∧ (lam t).w i ≤ hi t :=
    fun t i => weight_bounds hn (lam t) (hW t) i
  have hop := opBound l ι E n hn σ hσ lam hlam w hw hun (fun t => lo t + ((n : ℤ) - 1)) hi hlh
  have hPhi : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t) :=
    Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
  have hPlo : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) :=
    Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _

  have hroot : ∀ x ∈ algSat n (normV w) B, nu ι x ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t) := by
    refine roots_le ι hq1 hPhi _ fun j _ hj => ?_
    have hjn : j ≤ n := by simpa [algSat, hcard] using hj
    obtain ⟨s, s', hs, hs', he⟩ := hE j hjn
    refine ⟨((normV w : ℂ) ^ j.choose 2)⁻¹ * (algSat n (normV w) B).esymm j,
      mul_inv_cancel_left₀ (pow_ne_zero _ hqne) _, ?_⟩
    refine (hop j s _ fun f hf hsph => ?_).1 hs
    rw [mul_smul, ← (he f hf hsph).1, inv_smul_smul₀ (pow_ne_zero _ hqne)]

  have hinv : ∀ x ∈ algSat n (normV w) (B.map (·⁻¹)),
      nu ι x ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) := by
    refine roots_le ι hq1 hPlo _ fun j _ hj => ?_
    have hjn : j ≤ n := by simpa [algSat, hcard] using hj
    obtain ⟨s, s', hs, hs', he⟩ := hE j hjn
    refine ⟨((normV w : ℂ) ^ j.choose 2)⁻¹ * (algSat n (normV w) (B.map (·⁻¹))).esymm j,
      mul_inv_cancel_left₀ (pow_ne_zero _ hqne) _, ?_⟩
    refine (hop j s' _ fun f hf hsph => ?_).2 hs'
    rw [mul_smul, ← (he f hf hsph).2, inv_smul_smul₀ (pow_ne_zero _ hqne)]
  constructor
  · have h1 := hroot b hb
    have h2 : (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-hi t)) *
        ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t ht => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hvne t ht))]
    have h3 : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t :=
      Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
    show nu ι b * ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ hi t ≤ 1
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 h3
  · have hb2 : b ∈ B.map (fun α : ℂˣ => ((((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) * (α : ℂ)) := by
      rwa [algSat_as_map] at hb
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb2
    set r : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have hr2 : r ^ 2 = (normV w : ℂ) ^ (n - 1) := sq_factor (normV w) n hn
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hr2
      exact pow_ne_zero _ hqne (by simpa using hr2.symm)
    have hαne : (α : ℂ) ≠ 0 := α.ne_zero
    have hmem : r * ((α⁻¹ : ℂˣ) : ℂ) ∈ algSat n (normV w) (B.map (·⁻¹)) :=
      by
      rw [algSat_as_map]
      exact Multiset.mem_map.2 ⟨α⁻¹, Multiset.mem_map.2 ⟨α, hα, rfl⟩, rfl⟩
    have h1 := hinv _ hmem
    have hb' : (r * (α : ℂ))⁻¹ * (normV w : ℂ) ^ (n - 1) = r * ((α⁻¹ : ℂˣ) : ℂ) := by
      rw [← hr2, Units.val_inv_eq_inv_val]
      field_simp
    rw [← hb', nu_mul', nu_pow'] at h1
    have hsplit : ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (lo t + ((n : ℤ) - 1)) =
        (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ lo t) * nu ι (normV w : ℂ) ^ (n - 1) := by
      rw [← hprod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun t ht => ?_
      have : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      rw [zpow_add₀ (hvne t ht), this, zpow_natCast]
    rw [hsplit] at h1
    have h2 := le_of_mul_le_mul_right h1 (pow_pos hq0 _)
    have h3 : (∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ lo t) *
        ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t ht => ?_
      rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (hvne t ht))]
    have h4 : 0 ≤ ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) :=
      Finset.prod_nonneg fun t ht => zpow_nonneg (hv t ht).1.le _
    show nu ι (r * (α : ℂ))⁻¹ * ∏ t ∈ Ov ι w, nu ι (t (unif w : E)) ^ (-lo t) ≤ 1
    rw [← h3]
    exact mul_le_mul_of_nonneg_right h2 h4

end UpperTheory.V.Z.Int
