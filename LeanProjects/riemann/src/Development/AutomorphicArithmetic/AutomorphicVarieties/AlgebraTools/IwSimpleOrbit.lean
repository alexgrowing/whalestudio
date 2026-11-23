import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

private noncomputable def elem {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) : GL (Fin n) R :=
  ⟨1 + single i j a, 1 - single i j a,
    by simp [add_mul, mul_sub, single_mul_single_of_ne _ _ _ _ h.symm],
    by simp [sub_mul, mul_add, single_mul_single_of_ne _ _ _ _ h.symm]⟩

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b
      = (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv]
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq]
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem res_zero (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

private theorem pm_KO (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  show algebraMap 𝒪[k] k ((pm 𝒪[k] n w : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem conj_mem {C : Subgroup 𝓀[k]ˣ} {i j : Fin n} (hij : (j : ℕ) = i + 1) {g : GL (Fin n) k}
    (hg : g ∈ iwC k n C) :
    (pm k n (Equiv.swap i j))⁻¹ * g * pm k n (Equiv.swap i j) ∈ iwC k n C ↔
      valuation k ((g : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  have hm := (memIwC k n C).1
  obtain ⟨h1, h2⟩ := (hm g).1 hg
  obtain ⟨h3, h4⟩ := mem_iwahori.1 h1
  have hlt : i < j := by rw [Fin.lt_def]; omega
  constructor
  · intro h
    have := (mem_iwahori.1 ((hm _).1 h).1).2 j i hlt
    rwa [conj_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this
  · intro h
    refine (hm _).2 ⟨mem_iwahori.2 ⟨mul_mem (mul_mem (inv_mem (pm_KO _)) h3) (pm_KO _), fun a b hab => ?_⟩,
      fun a => ?_⟩
    · rw [conj_apply]
      by_cases hc : a = j ∧ b = i
      · rwa [hc.1, hc.2, Equiv.swap_apply_left, Equiv.swap_apply_right]
      · apply h4
        simp only [Equiv.swap_apply_def]
        simp only [Fin.ext_iff, Fin.lt_def] at *
        split_ifs <;> omega
    · rw [conj_apply]
      exact h2 _

private theorem pick {C : Subgroup 𝓀[k]ˣ} {g : GL (Fin n) k} (hg : g ∈ iwC k n C)
    {r : 𝓀[k] → 𝒪[k]} (hr : ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) (a i j : Fin n) :
    ∃ c, valuation k ((g : Matrix (Fin n) (Fin n) k) i j
      - algebraMap 𝒪[k] k (r c) * (g : Matrix (Fin n) (Fin n) k) a a) < 1 := by
  obtain ⟨h1, h2⟩ := ((memIwC k n C).1 g).1 hg
  obtain ⟨_, ⟨u, -, rfl⟩, hu⟩ := h2 a
  obtain ⟨h, rfl⟩ := (mem_iwahori.1 h1).1
  refine ⟨IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ)), ?_⟩
  rw [← hu]
  have := (res_zero ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
    r (IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ))) * (u : 𝒪[k]))).1 (by
      rw [map_sub, map_mul, hr, ← map_mul, Units.inv_mul_cancel_right, sub_self])
  rw [map_sub, map_mul] at this
  exact this

private theorem elem_mem {i j : Fin n} (h : i < j) (a : 𝒪[k]) :
    elem h.ne (algebraMap 𝒪[k] k a) ∈ unipO k n := by
  refine ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b _ _ hab => ?_, fun a _ _ => ?_⟩, elem h.ne a, ?_⟩
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a b = 0
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab h.asymm
    simp [one_apply_ne hab.ne', single_apply, this]
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a a = _
    have : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, rfl⟩
      exact h.ne rfl
    simp [single_apply, this]
  · ext p q
    show algebraMap 𝒪[k] k ((1 + single i j a : Matrix (Fin n) (Fin n) 𝒪[k]) p q) =
      (1 + single i j _ : Matrix (Fin n) (Fin n) k) p q
    simp only [Matrix.add_apply, one_apply, single_apply, map_add]
    split_ifs <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.simpleOrbit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (i j : Fin n), (j : ℕ) = i + 1 → ∀ (r : 𝓀[k] → 𝒪[k]), (∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) → ∃ x : 𝓀[k] → GL (Fin n) k, (∀ c, (x c : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j (algebraMap 𝒪[k] k (r c))) ∧ (∀ c, x c ∈ unipO k n) ∧ (∀ q : GL (Fin n) k ⧸ iwC k n C, q ∈ MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ↔ ∃! c, ((x c * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = q) ∧ ∀ g ∈ iwC k n C, ∃ c, ∃ b ∈ iwC k n C, pm k n (Equiv.swap i j) * g = b * (pm k n (Equiv.swap i j) * x c) := by
  intro k _ _ _ _ n C i j hij r hr
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hle : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right
  have hx : ∀ c, elem hlt.ne (algebraMap 𝒪[k] k (r c)) ∈ iwC k n C := fun c => hle (elem_mem hlt _)
  have hL : ∀ (a : k) (g : GL (Fin n) k), (((elem hlt.ne a)⁻¹ * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) j j := by
    intro a g
    show ((1 - single i j a) * (g : Matrix (Fin n) (Fin n) k)) i j = _
    simp [sub_mul]
  have hR : ∀ (a : k) (g : GL (Fin n) k), ((g * (elem hlt.ne a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) i i := by
    intro a g
    show ((g : Matrix (Fin n) (Fin n) k) * (1 - single i j a)) i j = _
    simp [mul_sub, mul_comm]
  have hs : (pm k n (Equiv.swap i j))⁻¹ = pm k n (Equiv.swap i j) := by rw [← map_inv, Equiv.swap_inv]
  refine ⟨fun c => elem hlt.ne (algebraMap 𝒪[k] k (r c)), fun c => rfl, fun c => elem_mem hlt _, fun q => ?_,
    fun g hg => ?_⟩
  · constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨c, hc⟩ := pick hg hr j i j
      have h1 : ((elem hlt.ne (algebraMap 𝒪[k] k (r c)) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
          GL (Fin n) k ⧸ iwC k n C) = ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) := by
        rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ g, ← mul_assoc]
        exact (conj_mem hij (mul_mem (inv_mem (hx c)) hg)).2 (by rwa [hL])
      refine ⟨c, h1, fun d hd => ?_⟩
      have h2 := h1.trans (Eq.symm hd)
      rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ (elem _ _), ← mul_assoc,
        conj_mem hij (mul_mem (inv_mem (hx c)) (hx d)), hL] at h2
      have h3 : valuation k (algebraMap 𝒪[k] k (r d - r c)) < 1 := by
        convert h2 using 2
        simp [elem, one_apply_ne hlt.ne, single_apply, hlt.ne]
      have h4 := (res_zero _).2 h3
      rwa [map_sub, hr, hr, sub_eq_zero] at h4
    · rintro ⟨c, rfl, -⟩
      exact ⟨⟨_, hx c⟩, rfl⟩
  · obtain ⟨c, hc⟩ := pick hg hr i i j
    refine ⟨c, _, (conj_mem hij (mul_mem hg (inv_mem (hx c)))).2 (by rwa [hR]), ?_⟩
    rw [mul_assoc, ← mul_assoc (pm k n _) (pm k n _), ← map_mul, Equiv.swap_mul_self, map_one, one_mul, hs,
      mul_assoc, inv_mul_cancel_right]
