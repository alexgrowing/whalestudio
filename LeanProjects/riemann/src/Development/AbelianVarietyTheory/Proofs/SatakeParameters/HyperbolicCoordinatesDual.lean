import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_inj_lt (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {a b : ℕ} (hab : a ≤ b) (hb : b < nP D p)
    (he : posPl D p z a = posPl D p z b) : a = b := by
  have h1 : posPl D p (posPl D p z a) (b - a) = posPl D p z a := by
    rw [posPl_add, Nat.add_sub_cancel' hab, he]
  have hd := posPl_fix D p _ _ h1
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem orbMap_inj (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {s s' : ZMod (nP D p)}
    (he : posPl D p z s.val = posPl D p z s'.val) : s = s' := by
  apply ZMod.val_injective
  rcases le_total s.val s'.val with h | h
  · exact posPl_inj_lt D p z h (ZMod.val_lt _) he
  · exact (posPl_inj_lt D p z h (ZMod.val_lt _) he.symm).symm

theorem iterate_mul_ringHom {K : Type*} [Semiring K] (σ : K →+* K) (m : ℕ) (x y : K) :
    σ^[m] (x * y) = σ^[m] x * σ^[m] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem fOf_fOf'_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  intro D p _ σ om oms R N N' r g h hOK hR hTr hσg hpair e e'
  obtain ⟨⟨⟨r0, hr0⟩, k⟩, a, b⟩ := e
  obtain ⟨⟨⟨r1, hr1⟩, k'⟩, a', b'⟩ := e'
  obtain ⟨m, hm⟩ := hOK.even
  have hn2 := hOK.two
  have hval : ∀ t : ZMod (nP D p), t.val % 2 = 0 → (t + 1).val = t.val + 1 := by
    intro t ht
    have hlt := ZMod.val_lt t
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < nP D p by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have reps : ∀ (m0 m1 : ℕ), posPl D p r0 m0 = posPl D p r1 m1 → r0 = r1 := fun m0 m1 he =>
    (hR (posPl D p r1 m1)).unique ⟨hr0, m0, he⟩ ⟨hr1, m1, rfl⟩
  have hf : ∀ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) * h (posPl D p r0 (t.val + 1)) a b i := by
    intro i
    simp only [fOf, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rw [map_mul, hσg, ← Function.iterate_succ_apply' σ, OrbitPlaces.orbMap, posPl_add]
    · simp
  have hf' : ∀ i, fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then 0 else σ^[t.val] (oms k')) * g (posPl D p r1 t.val) a' b' i := by
    intro i
    simp only [fOf', OrbitPlaces.orbMap]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  have h2 : ∑ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) * fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i =
      ∑ t : ZMod (nP D p), ∑ t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hf i, hf' i, Finset.sum_mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [← hpair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ t t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) =
      if t' = t + 1 then (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) *
        (if r0 = r1 ∧ a = a' ∧ b = b' then 1 else 0) else 0 := by
    intro t t'
    by_cases ht : t.val % 2 = 0
    · have h1 := hval t ht
      by_cases htt : t' = t + 1
      · subst htt
        have hodd : ¬ (t.val + 1) % 2 = 0 := by omega
        rw [if_pos rfl, h1, if_pos ht, if_pos ht, if_neg hodd, iterate_mul_ringHom]
        by_cases hc : r0 = r1 ∧ a = a' ∧ b = b'
        · obtain ⟨rfl, rfl, rfl⟩ := hc
          simp
        · rw [if_neg hc, if_neg]
          rintro ⟨hp, ha, hb⟩
          exact hc ⟨reps _ _ hp, ha, hb⟩
      · rw [if_neg htt]
        by_cases ht' : t'.val % 2 = 0
        · simp [ht']
        · by_cases hc : posPl D p r0 (t.val + 1) = posPl D p r1 t'.val
          · exfalso
            have hr := reps _ _ hc
            subst hr
            rw [← h1] at hc
            exact htt (orbMap_inj D p r0 hc).symm
          · simp [hc]
    · simp [ht]
  rw [h2, Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => key t t']
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  have h3 : ∑ t : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) =
      σ (∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om k * oms k') else 0) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · rw [Function.iterate_succ_apply']
    · simp
  rw [h3, hTr.2 k k']
  by_cases hk : k = k' <;> by_cases hr : r0 = r1 <;> by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [hk, hr, ha, hb]

end GlobalTheory.KerStd.HypCoord
