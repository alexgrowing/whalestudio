import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PrimEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.FactEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MinPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IntMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LeJoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MuLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LyOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.DerZero

noncomputable section

open Polynomial

namespace UpperTheory.V.J

private lemma rm_prod {K ι : Type} [Field K] (S : Finset ι) (f : ι → K[X]) (hf : ∀ i ∈ S, f i ≠ 0) (a : K) :
    rootMultiplicity a (∏ i ∈ S, f i) = ∑ i ∈ S, rootMultiplicity a (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have h1 : f j ≠ 0 := hf j (Finset.mem_insert_self j S)
    have h2 : ∏ i ∈ S, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [rootMultiplicity_mul (mul_ne_zero h1 h2), ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma rm_pow {K : Type} [Field K] (f : K[X]) (hf : f ≠ 0) (a : K) (n : ℕ) :
    rootMultiplicity a (f ^ n) = n * rootMultiplicity a f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih, Nat.succ_mul]

private lemma rm_map_prod {Λ K : Type} [CommRing Λ] [Field K] (φ : Λ →+* K) {s : ℕ} (g : Fin s → Λ[X])
    (hg : ∀ i, (g i).Monic) (m : Fin s → ℕ) (z : K) :
    rootMultiplicity z ((∏ i, g i ^ m i).map φ) = ∑ i, m i * rootMultiplicity z ((g i).map φ) := by
  have hne : ∀ i, (g i).map φ ≠ 0 := fun i => ((hg i).map φ).ne_zero
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_pow]
  rw [rm_prod _ _ (fun i _ => pow_ne_zero _ (hne i))]
  exact Finset.sum_congr rfl fun i _ => rm_pow _ (hne i) z (m i)

private lemma num_core {s : ℕ} (k m : Fin s → ℕ) (N : ℕ) (hm : ∀ i, 1 ≤ m i)
    (hsum : ∑ i, m i * k i ≤ N) (hle : ∀ i, 0 < k i → N ≤ m i) (hex : ∃ i, 0 < k i) :
    ∑ i, k i = 1 := by
  obtain ⟨i0, hi0⟩ := hex
  have hN : 1 ≤ N := by
    have h0 : m i0 * k i0 ≤ ∑ i, m i * k i :=
      Finset.single_le_sum (f := fun i => m i * k i) (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
    have hp : 0 < m i0 * k i0 := Nat.mul_pos (hm i0) hi0
    omega
  have h1 : N * ∑ i, k i ≤ N := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hsum
    rcases Nat.eq_zero_or_pos (k i) with h0 | hp
    · simp [h0]
    · exact Nat.mul_le_mul_right _ (hle i hp)
  have h2 : ∑ i, k i ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : N * 2 ≤ N * ∑ i, k i := Nat.mul_le_mul_left _ hc
    omega
  have h3 : k i0 ≤ ∑ i, k i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
  omega

private lemma not_dvd_der {Λ : Type} [CommRing Λ] [IsDomain Λ] [CharZero Λ] (g : Λ[X]) (hg : g.Monic)
    (hd : 0 < g.natDegree) : ¬ g ∣ derivative g := by
  intro hdvd
  have hne : derivative g ≠ 0 := fun h0 => by
    have := natDegree_eq_zero_of_derivative_eq_zero h0
    omega
  have h1 := natDegree_le_of_dvd hdvd hne
  have h2 := natDegree_derivative_lt (p := g) (by omega)
  omega

private lemma mem_cmp {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
    (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X]) (i : Fin s) (a : B) :
    a ∈ cmp lam J t g i ↔ a * (∏ j ∈ Finset.univ.erase i, g j).eval₂ (lam : Λ →+* B) t ∈ J := by
  unfold cmp
  rw [Submodule.mem_colon_singleton, smul_eq_mul]

private lemma ev {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B]
    [Algebra O K] (lam : Λ →ₐ[O] B) (y : B →ₐ[O] K) (q : Λ[X]) (t : B) :
    y (q.eval₂ (lam : Λ →+* B) t) = (q.map (y.comp lam : Λ →+* K)).eval (y t) := by
  rw [eval_map]
  exact hom_eval₂ q (lam : Λ →+* B) (y : B →+* K) t

private lemma comp_bound {O Λ B K : Type} [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X])
    (hC : Cmp lam J t g) (x : B →ₐ[O] K) (hS : Sep lam J x t) (i : Fin s)
    (hk : 0 < rootMultiplicity (x t) ((g i).map (x.comp lam : Λ →+* K))) : cmp lam J t g i ≤ RingHom.ker x := by
  have hne : (g i).map (x.comp lam : Λ →+* K) ≠ 0 := ((hC.monic i).map _).ne_zero
  have hroot := (rootMultiplicity_pos hne).1 hk
  have hev : eval₂ ((x.comp lam : Λ →ₐ[O] K) : Λ →+* K) (x t) (g i) = 0 := by
    rw [← eval_map]
    exact hroot
  obtain ⟨x', hx', hc, ht⟩ := lyOver O Λ B K lam J t s g hC (x.comp lam) (x t) i hev
  have hJc : J ≤ cmp lam J t g i := fun a ha => (mem_cmp lam J t g i a).2 (J.mul_mem_right _ ha)
  have hxx := hS x' (le_trans hJc hx') hc ht
  rw [← hxx]
  exact hx'

private lemma good_point {O Λ B K : Type} [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Field K]
    [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X])
    (hC : Cmp lam J t g) (y : B →ₐ[O] K) (hJ : J ≤ RingHom.ker y) (i : Fin s)
    (hd : y ((derivative (g i)).eval₂ (lam : Λ →+* B) t) ≠ 0)
    (he : y ((∏ j ∈ Finset.univ.erase i, g j).eval₂ (lam : Λ →+* B) t) ≠ 0) (m : Fin s → ℕ) :
    ∑ j, m j * rootMultiplicity (y t) ((g j).map (y.comp lam : Λ →+* K)) = m i := by
  rw [ev] at hd he
  have hk := RingHom.mem_ker.1 (hJ hC.kill)
  rw [ev] at hk
  set φ : Λ →+* K := (y.comp lam : Λ →+* K) with hφ
  have hgi : eval (y t) ((g i).map φ) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), Polynomial.map_mul, eval_mul] at hk
    exact (mul_eq_zero.1 hk).resolve_right he
  have hne : ∀ j, (g j).map φ ≠ 0 := fun j => ((hC.monic j).map _).ne_zero
  rw [Finset.sum_eq_single i]
  · have hpos : 0 < rootMultiplicity (y t) ((g i).map φ) := (rootMultiplicity_pos (hne i)).2 hgi
    have hle : ¬ 1 < rootMultiplicity (y t) ((g i).map φ) := by
      rw [one_lt_rootMultiplicity_iff_isRoot (hne i)]
      rintro ⟨_, h2⟩
      apply hd
      rw [Polynomial.derivative_map] at h2
      exact h2
    have h1 : rootMultiplicity (y t) ((g i).map φ) = 1 := by omega
    rw [h1, mul_one]
  · intro j _ hji
    rw [rootMultiplicity_eq_zero, mul_zero]
    intro hr
    apply he
    exact eval_eq_zero_of_dvd_of_eval_eq_zero
      (Polynomial.map_dvd φ (Finset.dvd_prod_of_mem g (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩))) hr
  · intro h
    exact absurd (Finset.mem_univ i) h

end UpperTheory.V.J

theorem UpperTheory.V.Z.Desc.V0.unrAlgW :
    UpperTheory.V.Z.Desc.V0.UnrAlgW := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h x hxJ 𝒢 b₀ hb₀ hG0 hG δ hδ hδJ hδl
  haveI := h.free
  haveI := h.fin
  obtain ⟨t, hP, hS⟩ := UpperTheory.V.J.primEx O Λ B K lam J M h x hxJ
  obtain ⟨s, g, m, hF⟩ :=
    UpperTheory.V.J.factEx Λ (LinearMap.charpoly (UpperTheory.V.J.actL lam M h.hs t)) (LinearMap.charpoly_monic _)
  obtain ⟨hkill, hmin⟩ := UpperTheory.V.J.minPol O Λ B lam J M h t s g m hF
  have hC : UpperTheory.V.J.Cmp lam J t g :=
    ⟨h.tf, UpperTheory.V.J.intMod O Λ B lam J M h, hP, hF.monic, hF.irr, hF.inj, hkill, hmin⟩
  have hsumAt : ∀ y : B →ₐ[O] K,
      rootMultiplicity (y t) ((LinearMap.charpoly (UpperTheory.V.J.actL lam M h.hs t)).map (y.comp lam : Λ →+* K)) =
        ∑ i, m i * rootMultiplicity (y t) ((g i).map (y.comp lam : Λ →+* K)) := by
    intro y
    rw [hF.prod]
    exact UpperTheory.V.J.rm_map_prod _ g hF.monic m (y t)
  have hge := UpperTheory.V.J.muGe O Λ B K lam J M h x t hS
  rw [hsumAt x] at hge
  have hex : ∃ i, 0 < rootMultiplicity (x t) ((g i).map (x.comp lam : Λ →+* K)) := by
    have hk := RingHom.mem_ker.1 (hxJ hkill)
    rw [UpperTheory.V.J.ev, Polynomial.map_prod, eval_prod, Finset.prod_eq_zero_iff] at hk
    obtain ⟨i, _, hi⟩ := hk
    exact ⟨i, (rootMultiplicity_pos ((hF.monic i).map _).ne_zero).2 hi⟩
  have hle : ∀ i, 0 < rootMultiplicity (x t) ((g i).map (x.comp lam : Λ →+* K)) →
      UpperTheory.V.J.mu lam M h.hs x ≤ m i := by
    intro i hki
    have hcx := UpperTheory.V.J.comp_bound lam J t g hC x hS i hki
    have hdeg : 0 < (g i).natDegree := by
      by_contra h0
      have h1 : g i = 1 := Polynomial.eq_one_of_monic_natDegree_zero (hF.monic i) (by omega)
      rw [h1, Polynomial.map_one] at hki
      simp at hki
    obtain ⟨y, hy𝒢, hyd, hye⟩ : ∃ y ∈ 𝒢,
        y ((derivative (g i)).eval₂ (lam : Λ →+* B) t) ≠ 0 ∧
          y ((∏ j ∈ Finset.univ.erase i, g j).eval₂ (lam : Λ →+* B) t) ≠ 0 := by
      by_contra hno
      push_neg at hno
      have hmem : (derivative (g i)).eval₂ (lam : Λ →+* B) t * b₀ ∈ UpperTheory.V.J.cmp lam J t g i := by
        rw [UpperTheory.V.J.mem_cmp, mul_right_comm]
        apply hG0
        intro y hy
        rw [map_mul]
        by_cases hd : y ((derivative (g i)).eval₂ (lam : Λ →+* B) t) = 0
        · rw [hd, zero_mul]
        · rw [hno y hy hd, mul_zero]
      obtain ⟨hprime, hiff, _⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g hC i
      rcases hprime.mem_or_mem hmem with h1 | h1
      · exact UpperTheory.V.J.not_dvd_der (g i) (hF.monic i) hdeg ((hiff _).1 h1)
      · exact hb₀ (RingHom.mem_ker.1 (hcx h1))
    have hgp := UpperTheory.V.J.good_point lam J t g hC y (hG y hy𝒢).1 i hyd hye m
    have hmu := UpperTheory.V.J.muLe O Λ B K lam M h.hs y t
    rw [hsumAt y, hgp] at hmu
    exact le_trans (hG y hy𝒢).2 hmu
  have hsum1 := UpperTheory.V.J.num_core (fun i => rootMultiplicity (x t) ((g i).map (x.comp lam : Λ →+* K))) m
    (UpperTheory.V.J.mu lam M h.hs x) hF.pos hge hle hex
  have hprod1 : rootMultiplicity (x t) ((∏ j, g j).map (x.comp lam : Λ →+* K)) = 1 := by
    have e := UpperTheory.V.J.rm_map_prod (x.comp lam : Λ →+* K) g hF.monic (fun _ => 1) (x t)
    simp only [pow_one, one_mul] at e
    rw [e]
    exact hsum1
  obtain ⟨i, hi⟩ := hex
  exact UpperTheory.V.J.derZero O Λ B K lam J t s g hC x i (UpperTheory.V.J.comp_bound lam J t g hC x hS i hi) hprod1
    δ hδ hδJ hδl

end
