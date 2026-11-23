import Formalism.SharpRestriction.GrowthBounds.PathWeight.FixedSymbolFactorIntegral

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem mn_cover {n' r : ℕ} [NeZero n'] (F : Frames n' r) (L₁ N₁ : ℕ) (hV : F.Valid L₁ N₁) (hr : 1 ≤ r) (x : ℤ)
    (hx : posOf n' x ∈ F.TT) : ∃ j : ℤ, x ∈ F.letters j ∧ ¬ F.IsW j x := by
  have hstep : ∀ j, F.fr j (r - 1) < F.fr (j + 1) (r - 1) := fun j =>
    lt_of_lt_of_le (hV.2.2.2.1 j) (frame_row_monotone F L₁ N₁ hV (j + 1) (r - 1) (by omega))
  have hup : ∀ t : ℕ, F.fr 0 (r - 1) + t ≤ F.fr (t : ℤ) (r - 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := hstep t
      push_cast
      omega
  have hdn : ∀ t : ℕ, F.fr (-(t : ℤ)) (r - 1) + t ≤ F.fr 0 (r - 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := hstep (-((t + 1 : ℕ) : ℤ))
      have e : -((t + 1 : ℕ) : ℤ) + 1 = -(t : ℤ) := by push_cast; ring
      rw [e] at h
      push_cast at h ⊢
      omega
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd (P := fun j => x ≤ F.fr j (r - 1))
    ⟨min 0 (x - F.fr 0 (r - 1)), by
      intro j hj
      by_cases h0 : 0 ≤ j
      · exact le_trans (min_le_left _ _) h0
      · have h := hdn (-j).toNat
        have e : -(((-j).toNat : ℕ) : ℤ) = j := by omega
        rw [e] at h
        refine le_trans (min_le_right _ _) ?_
        omega⟩
    ⟨((x - F.fr 0 (r - 1)).toNat : ℤ), by
      have h := hup (x - F.fr 0 (r - 1)).toNat
      show x ≤ F.fr _ (r - 1)
      omega⟩
  have hnot : ¬ x ≤ F.fr (j - 1) (r - 1) := fun h => by
    have := hmin (j - 1) h
    omega
  refine ⟨j, ?_, hnot⟩
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  have h1 := frame_row_monotone F L₁ N₁ hV (j - 1) (r - 1) (by omega)
  exact ⟨⟨by omega, hj⟩, hx⟩

section Mon

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

local notation "PP" => MvPolynomial (TV n' (r + K)) (KK O)

theorem mn_label_le (mon : Fin n' × Fin (r + K) →₀ ℕ) (hmon : IsLabel p X.Fr mon) (s : Fin n') (hs : s ∈ X.Fr.TT)
    (c : Fin (r + K)) : mon (s, c) ≤ X.Q := by
  have hr : 1 ≤ r := by have := X.hH.2.1; omega
  obtain ⟨j, hx, hW⟩ := mn_cover X.Fr X.L₁ X.N₁ X.hV hr (s.val : ℤ) (by rw [posOf_natCast_self]; exact hs)
  have h1 := hmon j (s.val : ℤ) hx hW c
  rw [posOf_natCast_self] at h1
  have h2 : X.Fr.dist j (s.val : ℤ) ≤ X.G' := by
    unfold Frames.letters at hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    have h3 := X.hG j
    unfold zF at h3
    unfold Frames.dist
    omega
  have h4 : p ^ X.Fr.dist j (s.val : ℤ) ≤ p ^ X.G' := Nat.pow_le_pow_right (Fact.out : p.Prime).pos h2
  unfold Ctx.Q
  omega

def Ctx.Ds (s : Fin n') : PP := X.sb (Dtop p n' O X.Fr X.hH.2.2.1 X.g (s.val : ℤ))

theorem mn_Ds_IT (s : Fin n') : bc_IT X.Fr (X.Ds s) := by
  have hr : 1 ≤ r := by have := X.hH.2.1; omega
  exact bc_IT_Dtop X.S.w X.Fr X.hV X.hH.2.2.2.2 hr X.hH.2.2.1 X.hg _

theorem leading_depth_one_mem_closure (D : Formalism.BasicNotions.D7) (v : TV n' (r + K)) (hN : IsNormal r v) (hs : v.1 ∈ X.Fr.TT) :
    C (algebraMap O (KK O) X.S.w) * MvPolynomial.X v * X.Ds v.1 ∈
      AddSubmonoid.closure (bc_agen X.S.w X.Fr X.Q X.g 1 0) := by
  obtain ⟨s, b⟩ := v
  obtain ⟨n, ka, ka0, H, hc, heq⟩ := segment_statement_holds D p n' r (r + K) O X.S X.hO X.hH X.Fr X.L₁ X.N₁ X.hV X.Q X.hT X.g X.hg
    s hs b hN
  have hwne : algebraMap O (KK O) X.S.w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 X.S.w_irr.ne_zero
  have hw1 : (C (algebraMap O (KK O) X.S.w) : PP) * C (wInv X.S.w) = 1 := by
    rw [← C_mul, wInv, mul_inv_cancel₀ hwne, C_1]
  have hsum : C (algebraMap O (KK O) X.S.w) * MvPolynomial.X (s, b) * X.Ds s =
      ∑ i, ka0 i * MvPolynomial.map (algebraMap O (KK O)) (H i) := by
    have e1 : C (algebraMap O (KK O) X.S.w) * MvPolynomial.X (s, b) * X.Ds s =
        C (algebraMap O (KK O) X.S.w) * (MvPolynomial.X (s, b) * X.Ds s) := by ring
    rw [e1]
    unfold Ctx.Ds Ctx.sb
    rw [heq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (MvPolynomial.map (algebraMap O (KK O)) (H i) * ka0 i) * hw1
  show C (algebraMap O (KK O) X.S.w) * MvPolynomial.X (s, b) * X.Ds s ∈ _
  rw [hsum]
  refine sum_mem fun i _ => AddSubmonoid.subset_closure ⟨ka0 i, _,
    isKeyProduct_of_isKey X.S.w X.Fr X.Q X.g (hc i).1 (hc i).2.2.1 (hc i).2.2.2.1,
    ⟨H i, fun v hv => ?_, (hc i).2.2.2.2, rfl⟩, rfl⟩
  have h1 := (hc i).2.1 v hv
  unfold IsNormal
  rw [if_pos h1.1]
  have := h1.2
  omega

theorem mn_DkQ_eq : X.DkQ = ∏ s ∈ X.Fr.TT, X.Ds s ^ ((r + K) * X.Q) := by
  unfold Ctx.DkQ DtopProd Ctx.Ds
  rw [map_prod]
  simp only [map_pow]

theorem mn_DkQ_IT : bc_IT X.Fr X.DkQ := by
  rw [mn_DkQ_eq]
  exact bc_IT_prod _ _ fun s _ => bc_IT_pow (mn_Ds_IT X s) _

def mn_ns (r : ℕ) {n' k : ℕ} (mon : TV n' k →₀ ℕ) (s : Fin n') : ℕ :=
  ∑ v ∈ (mon.support.filter (fun v => IsNormal r v)).filter (fun v => v.1 = s), mon v

theorem mn_ns_le (mon : Fin n' × Fin (r + K) →₀ ℕ) (hmon : IsLabel p X.Fr mon) (s : Fin n') (hs : s ∈ X.Fr.TT) :
    mn_ns r mon s ≤ (r + K) * X.Q := by
  unfold mn_ns
  have hcard : ((mon.support.filter (fun v => IsNormal r v)).filter (fun v => v.1 = s)).card ≤ r + K := by
    have h := Finset.card_le_card_of_injOn (s := (mon.support.filter (fun v => IsNormal r v)).filter (fun v => v.1 = s))
      (t := (Finset.univ : Finset (Fin (r + K)))) (fun v => v.2) (fun _ _ => Finset.mem_univ _) (by
        intro a ha b hb h
        have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        exact Prod.ext (h1.trans h2.symm) h)
    simpa using h
  calc _ ≤ ∑ _v ∈ (mon.support.filter (fun v => IsNormal r v)).filter (fun v => v.1 = s), X.Q := by
        refine Finset.sum_le_sum fun v hv => ?_
        have e := (Finset.mem_filter.1 hv).2
        obtain ⟨s', c⟩ := v
        simp only at e
        subst e
        exact mn_label_le X mon hmon _ hs c
    _ = ((mon.support.filter (fun v => IsNormal r v)).filter (fun v => v.1 = s)).card * X.Q := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (r + K) * X.Q := Nat.mul_le_mul_right _ hcard

theorem mn_X_IT (v : TV n' (r + K)) (hN : ¬ IsNormal r v) (hs : v.1 ∈ X.Fr.TT) :
    bc_IT X.Fr (MvPolynomial.X v : PP) :=
  ⟨MvPolynomial.X v, fun v' hv' => by
      rw [vars_X, Finset.mem_singleton] at hv'
      rw [hv']; exact hN,
    fun v' hv' => by
      rw [vars_X, Finset.mem_singleton] at hv'
      rw [hv']; exact hs, by simp⟩

theorem mn_main (D : Formalism.BasicNotions.D7) (mon : Fin n' × Fin (r + K) →₀ ℕ) (hmon : IsLabel p X.Fr mon)
    (hmonT : ∀ v ∈ mon.support, v.1 ∈ X.Fr.TT) :
    Sy X.S.w X.Fr X.Q X.g (normDeg r mon) (monomial mon 1 * X.DkQ) := by
  refine ⟨?_, ?_⟩
  · rw [hom_iff]
    have h1 : IsWeightedHomogeneous (normalVariableWeight n' (r + K) r) (monomial mon (1 : KK O)) (normDeg r mon) :=
      isWeightedHomogeneous_monomial _ mon 1 (weight_eq_normal_degree r mon)
    have h2 := h1.mul (IT_hom (mn_DkQ_IT X))
    simpa using h2
  · have ho : normDeg r mon = ∑ v ∈ mon.support.filter (fun v => IsNormal r v), mon v := by
      unfold normDeg
      rw [Finset.sum_filter]
    have hmonE : (monomial mon 1 : PP) =
        (∏ v ∈ mon.support.filter (fun v => IsNormal r v), MvPolynomial.X v ^ mon v) *
          ∏ v ∈ mon.support.filter (fun v => ¬ IsNormal r v), MvPolynomial.X v ^ mon v := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod, Finset.prod_filter_mul_prod_filter_not]
    have hDfib : ∏ v ∈ mon.support.filter (fun v => IsNormal r v), X.Ds v.1 ^ mon v =
        ∏ s ∈ X.Fr.TT, X.Ds s ^ mn_ns r mon s := by
      rw [← Finset.prod_fiberwise_of_maps_to (s := mon.support.filter (fun v => IsNormal r v)) (t := X.Fr.TT)
        (g := fun v => v.1) (fun v hv => hmonT v (Finset.mem_filter.1 hv).1)]
      refine Finset.prod_congr rfl fun s _ => ?_
      unfold mn_ns
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [(Finset.mem_filter.1 hv).2]
    have hC : (C (algebraMap O (KK O) (X.S.w ^ normDeg r mon)) : PP) =
        ∏ v ∈ mon.support.filter (fun v => IsNormal r v), C (algebraMap O (KK O) X.S.w) ^ mon v := by
      rw [Finset.prod_pow_eq_pow_sum, ← ho, map_pow, C_pow]
    have hDk : X.DkQ = (∏ s ∈ X.Fr.TT, X.Ds s ^ mn_ns r mon s) *
        ∏ s ∈ X.Fr.TT, X.Ds s ^ ((r + K) * X.Q - mn_ns r mon s) := by
      rw [mn_DkQ_eq, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [← pow_add, Nat.add_sub_cancel' (mn_ns_le X mon hmon s hs)]
    have hid : C (algebraMap O (KK O) (X.S.w ^ normDeg r mon)) * (monomial mon 1 * X.DkQ) =
        (∏ v ∈ mon.support.filter (fun v => IsNormal r v),
          (C (algebraMap O (KK O) X.S.w) * MvPolynomial.X v * X.Ds v.1) ^ mon v) *
        ((∏ v ∈ mon.support.filter (fun v => ¬ IsNormal r v), MvPolynomial.X v ^ mon v) *
          ∏ s ∈ X.Fr.TT, X.Ds s ^ ((r + K) * X.Q - mn_ns r mon s)) := by
      rw [hC, hmonE, hDk, ← hDfib]
      simp only [mul_pow, Finset.prod_mul_distrib]
      ring
    have hA : (∏ v ∈ mon.support.filter (fun v => IsNormal r v),
          (C (algebraMap O (KK O) X.S.w) * MvPolynomial.X v * X.Ds v.1) ^ mon v) ∈
        AddSubmonoid.closure (bc_agen X.S.w X.Fr X.Q X.g
          (∑ v ∈ mon.support.filter (fun v => IsNormal r v), mon v) 0) :=
      bc_gr_prod (bc_agen_mul X.S.w X.Fr X.Q X.g) (bc_agen_one X.S.w X.Fr X.Q X.g) _ _ (fun v => mon v)
        (fun v hv => by
          have := bc_gr_pow (bc_agen_mul X.S.w X.Fr X.Q X.g) (bc_agen_one X.S.w X.Fr X.Q X.g)
            (leading_depth_one_mem_closure X D v (Finset.mem_filter.1 hv).2 (hmonT v (Finset.mem_filter.1 hv).1)) (mon v)
          rw [smul_eq_mul, mul_one] at this
          exact this)
    have hB : bc_IT X.Fr ((∏ v ∈ mon.support.filter (fun v => ¬ IsNormal r v), (MvPolynomial.X v : PP) ^ mon v) *
          ∏ s ∈ X.Fr.TT, X.Ds s ^ ((r + K) * X.Q - mn_ns r mon s)) :=
      bc_IT_mul (bc_IT_prod _ _ fun v hv => bc_IT_pow
        (mn_X_IT X v (Finset.mem_filter.1 hv).2 (hmonT v (Finset.mem_filter.1 hv).1)) _)
        (bc_IT_prod _ _ fun s _ => bc_IT_pow (mn_Ds_IT X s) _)
    have hB' : ((∏ v ∈ mon.support.filter (fun v => ¬ IsNormal r v), (MvPolynomial.X v : PP) ^ mon v) *
          ∏ s ∈ X.Fr.TT, X.Ds s ^ ((r + K) * X.Q - mn_ns r mon s)) ∈
        AddSubmonoid.closure (bc_agen X.S.w X.Fr X.Q X.g 0 0) :=
      AddSubmonoid.subset_closure ⟨1, _, isKeyProduct_one X.S.w X.Fr X.Q X.g, hB, by rw [one_mul]⟩
    have hAB := bc_gr_mul (bc_agen_mul X.S.w X.Fr X.Q X.g) hA hB'
    rw [add_zero, add_zero] at hAB
    rw [hid, ho]
    exact hAB

end Mon

theorem restMon (D : Formalism.BasicNotions.D7) : RestMon := by
  intro p n' r K _ _ _ _ O _ _ _ _ X mon hmon hmonT
  exact ⟨normDeg r mon, mn_main X D mon hmon hmonT⟩

end Formalism.MainNotions.G.symbolGeneratorData
