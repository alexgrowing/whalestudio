import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLenStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools.PermCard

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv, Units.val_mul, Units.val_mul]
  simp only [mul_apply, pm_apply]
  rw [Fintype.sum_eq_single (w b), Fintype.sum_eq_single (w a)]
  · simp
  · intro x hx
    rw [if_neg, zero_mul]
    rintro rfl
    exact hx (by simp)
  · intro x hx
    rw [if_neg hx, mul_zero]

private theorem map_pm {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (w : Equiv.Perm (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) f (pm R n w) = pm S n w := by
  ext i j
  show f ((pm R n w : Matrix (Fin n) (Fin n) R) i j) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem ncard_orbit {G ι : Type} [Group G] (I : Subgroup G) (s w : G) (x : ι → G) (hx : ∀ c, x c ∈ I)
    (h1 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, g * s = x c * s * b)
    (h2 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, s * g = b * (s * x c))
    (h3 : ∀ c, w⁻¹ * x c * w ∈ I)
    (h4 : ∀ c c', ∀ g ∈ I, ∀ g' ∈ I, w⁻¹ * (g'⁻¹ * (s⁻¹ * ((x c')⁻¹ * x c) * s) * g) * w ∈ I → c = c') :
    (MulAction.orbit I ((s * w : G) : G ⧸ I)).ncard = Nat.card ι * (MulAction.orbit I (w : G ⧸ I)).ncard := by
  have hm : ∀ (c : ι) (q : MulAction.orbit I (w : G ⧸ I)),
      (x c * s) • (q : G ⧸ I) ∈ MulAction.orbit I ((s * w : G) : G ⧸ I) := by
    rintro c ⟨_, g, rfl⟩
    obtain ⟨a, b, hb, e⟩ := h2 g g.2
    refine ⟨⟨x c * b, mul_mem (hx c) hb⟩, ?_⟩
    show ((x c * b * (s * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I)
    rw [QuotientGroup.eq]
    have : x c * s * (g * w) = x c * (s * g) * w := by group
    rw [this, e]
    convert h3 a using 1
    group
  let f : ι × MulAction.orbit I (w : G ⧸ I) → MulAction.orbit I ((s * w : G) : G ⧸ I) :=
    fun p => ⟨_, hm p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, _, g, rfl⟩ ⟨c', _, g', rfl⟩ e
      have e1 : (x c * s) • ((g : G) • (w : G ⧸ I)) = (x c' * s) • ((g' : G) • (w : G ⧸ I)) :=
        congrArg Subtype.val e
      have e2 : ((x c' * s * (g' * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I) := e1.symm
      rw [QuotientGroup.eq] at e2
      have hc : c = c' := h4 c c' g g.2 g' g'.2 (by convert e2 using 1; group)
      subst hc
      exact Prod.ext rfl (Subtype.ext (smul_left_cancel _ e1))
    · rintro ⟨_, g, rfl⟩
      obtain ⟨c, b, hb, e⟩ := h1 g g.2
      refine ⟨(c, ⟨_, ⟨b, hb⟩, rfl⟩), Subtype.ext ?_⟩
      show ((x c * s * (b * w) : G) : G ⧸ I) = ((g * (s * w) : G) : G ⧸ I)
      rw [← mul_assoc, ← e, mul_assoc]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod, Nat.card_eq_of_bijective f hf]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem step (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) :
    (MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j * w) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard =
      resCard k * (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard := by
  choose r hr using IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨x, hx, hxu, ho, h2⟩ := simpleOrbit k n C i j hij r hr
  have hU : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨hmem, -, -, hun⟩ := memIwC k n C
  have hdiag : ∀ g ∈ iwC k n C, ∀ a, valuation k ((g : Matrix (Fin n) (Fin n) k) a a) = 1 := by
    intro g hg a
    obtain ⟨c, ⟨d, -, rfl⟩, e⟩ := ((hmem g).1 hg).2 a
    rw [← e]
    exact (hun _).1 ⟨d, trivial, rfl⟩
  have hlow : ∀ g ∈ iwC k n C, ∀ a b, b < a → valuation k ((g : Matrix (Fin n) (Fin n) k) a b) < 1 :=
    fun g hg => (mem_iwahori.1 ((hmem g).1 hg).1).2
  rw [map_mul]
  refine ncard_orbit (iwC k n C) _ _ x (fun c => hU (hxu c)) ?_ h2 ?_ ?_
  · intro g hg
    obtain ⟨c, hc, -⟩ := (ho ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).1
      ⟨⟨g, hg⟩, rfl⟩
    exact ⟨c, _, QuotientGroup.eq.1 hc, by group⟩
  · intro c
    have hK : pm k n w ∈ KO k (Fin n) := ⟨pm 𝒪[k] n w, map_pm _ w⟩
    have hK' : (pm k n w)⁻¹ * x c * pm k n w ∈ KO k (Fin n) := mul_mem (mul_mem (inv_mem hK) (hxu c).2) hK
    refine hU ⟨(mem_unipB k).2 ⟨fun a b hab => ?_, fun a => ?_⟩, hK'⟩
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_ne (w.injective.ne hab.ne'), single_apply, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hw
      exact lt_asymm hw hab
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_eq, single_apply, if_neg, add_zero]
      rintro ⟨h, h'⟩
      exact hlt.ne (h.trans h'.symm)
  · intro c c' g hg g' hg' h
    set d : k := algebraMap 𝒪[k] k (r c) - algebraMap 𝒪[k] k (r c') with hd
    have hz : (((x c')⁻¹ * x c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 + single i j d := by
      rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul, hx, hx, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
        single_mul_single_of_ne _ _ _ _ hlt.ne', add_zero, add_assoc, ← single_add, hd, sub_add_cancel]
    have hy : (((pm k n (Equiv.swap i j))⁻¹ * ((x c')⁻¹ * x c) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 1 + single j i d := by
      ext a b
      rw [conj_apply, hz]
      simp only [Matrix.add_apply, one_apply, single_apply, Equiv.apply_eq_iff_eq]
      congr 2
      rw [← Equiv.symm_apply_eq, ← Equiv.symm_apply_eq, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
    have h5 := hlow _ h _ _ hw
    rw [conj_apply, Units.val_mul, Units.val_mul, hy, mul_add, add_mul, mul_one, Matrix.add_apply] at h5
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h5
    have h6 := hlow _ (mul_mem (inv_mem hg') hg) j i hlt
    rw [Units.val_mul] at h6
    have h7 : (((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * single j i d * (g : Matrix (Fin n) (Fin n) k)) j i =
        ((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) j j * d * (g : Matrix (Fin n) (Fin n) k) i i := by
      rw [mul_apply, Fintype.sum_eq_single i, mul_single_apply_same]
      intro a ha
      rw [mul_single_apply_of_ne _ _ _ _ _ ha, zero_mul]
    have h8 := Valuation.map_sub_lt _ h5 h6
    rw [add_sub_cancel_left, h7, map_mul, map_mul, hdiag _ (inv_mem hg'), hdiag _ hg, one_mul, mul_one, hd,
      ← map_sub] at h8
    have h9 : IsLocalRing.residue 𝒪[k] (r c - r c') = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact h8.ne
    rwa [map_sub, hr, hr, sub_eq_zero] at h9

end UpperTheory.V.AlgebraTools.PermCard

open UpperTheory.V.AlgebraTools.PermCard in
theorem UpperTheory.V.AlgebraTools.permCard :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)), (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = resCard k ^ invLen w := by
  intro k _ _ _ _ n C w
  generalize hm : invLen w = m
  induction m generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 hm, map_one, pow_zero, Set.ncard_eq_one]
    refine ⟨_, Set.eq_singleton_iff_unique_mem.2 ⟨MulAction.mem_orbit_self _, ?_⟩⟩
    rintro _ ⟨g, rfl⟩
    show (((g : GL (Fin n) k) * 1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = _
    rw [QuotientGroup.eq]
    simpa using g.2
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        rw [invLen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun p _ h => lt_asymm h.1 h.2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hl := ((lenStep n w).1 i j hij).2 hlt
    have hs := step C (Equiv.swap i j * w) i j hij (by simpa using hlt)
    rw [Equiv.swap_mul_self_mul] at hs
    rw [hs, ih _ (by omega), pow_succ']
