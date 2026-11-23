import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA

section Act

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem dLin_addOf (F : Fin d → PS k 2 d)
    (hF0 : ∀ i l, coeff (Finsupp.single ((0 : Fin 2), l) 1) (F i) = if l = i then 1 else 0)
    (hF1 : ∀ i l, coeff (Finsupp.single ((1 : Fin 2), l) 1) (F i) = if l = i then 1 else 0)
    (u v : Pt k 1 d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    dLin (addOf F u v) = dLin u + dLin v := by
  classical
  ext i j
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![u, v] (F i)) = dLin u i j + dLin v i j
  rw [coeff_lin_ev _ (by
      intro a i'
      fin_cases a
      · exact hu i'
      · exact hv i')]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hF0, hF1, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem const_actK' (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by
  simp [FB.actK, B.A.const]

theorem actK_add (B : FB R d O) (a b : O) :
    B.actK k (a + b) = addOf (B.FK k) (B.actK k a) (B.actK k b) := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act (a + b) i) = ev ![B.actK k a, B.actK k b] (B.FK k i)
  rw [B.A.add_act]
  show MvPowerSeries.map (algebraMap R k) (ev ![B.A.act a, B.A.act b] (B.G.F i)) = _
  rw [Nab.map_ev (algebraMap R k) (by
      intro j l
      fin_cases j
      · exact B.A.const a l
      · exact B.A.const b l)]
  congr 1
  funext j l
  fin_cases j <;> rfl

theorem actK_mul (B : FB R d O) (a b : O) : B.actK k (a * b) = comp1 (B.actK k a) (B.actK k b) := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act (a * b) i) = ev ![B.actK k b] (B.actK k a i)
  rw [B.A.mul_act]
  show MvPowerSeries.map (algebraMap R k) (ev ![B.A.act b] (B.A.act a i)) = _
  rw [Nab.map_ev (algebraMap R k) (by
      intro j l
      fin_cases j
      exact B.A.const b l)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem actK_one (B : FB R d O) : B.actK k 1 = pt k d 0 := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act 1 i) = X ((0 : Fin 1), i)
  rw [B.A.one_act]
  simp [pt]

theorem biext_coeff_first_linear (B : FB R d O) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (B.FK k i) = if l = i then 1 else 0 := by
  show coeff _ (MvPowerSeries.map (algebraMap R k) (B.G.F i)) = _
  rw [coeff_map, formal_group_coeff_first_linear]
  split_ifs <;> simp

theorem biext_coeff_second_linear (B : FB R d O) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (B.FK k i) = if l = i then 1 else 0 := by
  show coeff _ (MvPowerSeries.map (algebraMap R k) (B.G.F i)) = _
  rw [coeff_map, formal_group_coeff_second_linear]
  split_ifs <;> simp

theorem dAct_add (B : FB R d O) (a b : O) : dAct k B (a + b) = dAct k B a + dAct k B b := by
  show dLin (B.actK k (a + b)) = dLin (B.actK k a) + dLin (B.actK k b)
  rw [actK_add, dLin_addOf k _ (biext_coeff_first_linear k B) (biext_coeff_second_linear k B) _ _ (const_actK' k B a) (const_actK' k B b)]

theorem dAct_mul (B : FB R d O) (a b : O) : dAct k B (a * b) = dAct k B a * dAct k B b := by
  show dLin (B.actK k (a * b)) = dLin (B.actK k a) * dLin (B.actK k b)
  rw [actK_mul, dLin_comp1 _ _ (const_actK' k B b)]

theorem dAct_one (B : FB R d O) : dAct k B 1 = 1 := by
  show dLin (B.actK k 1) = 1
  rw [actK_one, dLin_pt]

def dActH (B : FB R d O) : O →+* Matrix (Fin d) (Fin d) k where
  toFun a := dAct k B a
  map_one' := dAct_one k B
  map_mul' a b := dAct_mul k B a b
  map_zero' := by
    have h0 := dAct_add k B 0 0
    rw [add_zero] at h0
    simpa using h0
  map_add' a b := dAct_add k B a b

def dActS (B : FB R d O) : O →+* Matrix (Fin d) (Fin d) k where
  toFun a := (dActH k B (star a)).transpose
  map_one' := by rw [star_one, map_one, Matrix.transpose_one]
  map_mul' a b := by rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by rw [star_zero, map_zero, Matrix.transpose_zero]
  map_add' a b := by rw [star_add, map_add, Matrix.transpose_add]

theorem OactH_eq (B : FB R d O) (a : O) (ξ : (Fin d → k) × (Fin d → k)) :
    OactH k B a ξ = ((dActH k B a).mulVec ξ.1, (dActS k B a).mulVec ξ.2) := rfl

end Act

section H

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d)

theorem hset_zero : (0 : (Fin d → k) × (Fin d → k)) ∈ Hset (R := R) k h := by
  refine ⟨0, 0, Prod.ext ?_ ?_⟩ <;> funext i <;> simp [Matrix.mulVec, dotProduct]

theorem hset_add {ξ η : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) (hη : η ∈ Hset (R := R) k h) :
    ξ + η ∈ Hset (R := R) k h := by
  obtain ⟨u, φ, rfl⟩ := hξ
  obtain ⟨u', φ', rfl⟩ := hη
  refine ⟨u + u', φ + φ', Prod.ext ?_ ?_⟩ <;> funext i
  · simp
  · simp only [Prod.snd_add, Pi.add_apply, map_add]
    rw [show (fun j => algebraMap R k (u j) + algebraMap R k (u' j)) =
        (fun j => algebraMap R k (u j)) + (fun j => algebraMap R k (u' j)) from rfl, Matrix.mulVec_add, Pi.add_apply]
    ring

theorem hset_smul (c : R) {ξ : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) :
    algebraMap R k c • ξ ∈ Hset (R := R) k h := by
  obtain ⟨u, φ, rfl⟩ := hξ
  refine ⟨c • u, c • φ, Prod.ext ?_ ?_⟩ <;> funext i
  · simp [Algebra.smul_def]
  · have hv : (fun j => algebraMap R k ((c • u) j)) = algebraMap R k c • fun j => algebraMap R k (u j) := by
      funext j
      simp
    rw [hv, Matrix.mulVec_smul]
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul]
    ring

theorem hset_sum {ι : Type} (s : Finset ι) (f : ι → (Fin d → k) × (Fin d → k))
    (hf : ∀ i ∈ s, f i ∈ Hset (R := R) k h) : ∑ i ∈ s, f i ∈ Hset (R := R) k h :=
  Finset.sum_induction _ (· ∈ Hset (R := R) k h) (fun _ _ => hset_add k h) (hset_zero k h) hf

end H

theorem idem_eig {d : ℕ} {O k : Type} [CommRing O] [CommRing k] (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k)
    {n : ℕ} (b : Fin n → O) (c : Fin n → k) (a : O) (m : Fin n → Fin n → ℤ)
    (hb : ∀ i, a * b i = ∑ j, m i j • b j) (hc : ∀ j, ∑ i, (m i j : k) * c i = χ a * c j) :
    M a * ∑ i, c i • M (b i) = χ a • ∑ i, c i • M (b i) := by
  have h1 : ∀ i, M a * (c i • M (b i)) = ∑ j, (c i * (m i j : k)) • M (b j) := by
    intro i
    rw [Matrix.mul_smul, ← map_mul, hb i, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul k, smul_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, smul_smul, ← hc j]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eigLift_core {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [Field k]
    [Algebra ℚ k] [Algebra R k] (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty : Type} (ty : L → Ty) (χ : Ty → O →+* k) (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) =
      χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (hidem : ∀ t : Ty, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * χ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = χ t a * algebraMap R k (c j)) :
    ∃ φ : L → Fin d → R, ∀ ℓ ℓ', (∃ a, χ (ty ℓ) a ≠ χ (ty ℓ') (star a)) →
      ∑ i, (algebraMap R k (φ ℓ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
  classical
  have key : ∀ ℓ' : L, ∃ φ' : Fin d → R, ∀ ℓ : L, (∃ a, χ (ty ℓ) a ≠ χ (ty ℓ') (star a)) →
      ∑ i, (algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
    intro ℓ'
    obtain ⟨n, b, c, hnorm, hm⟩ := hidem (ty ℓ')
    set U : Fin d → k := fun i => algebraMap R k (u ℓ' i) with hUdef
    set ξ0 : (Fin d → k) × (Fin d → k) := (U, -(sg1 k h).mulVec U) with hξ0def
    set ξ1 : (Fin d → k) × (Fin d → k) :=
      ((∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U,
        (∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)) with hξ1def
    have hξ0 : ξ0 ∈ Hset (R := R) k h := ⟨u ℓ', 0, Prod.ext rfl (by funext i; simp [hξ0def, hUdef])⟩
    have hsum : ξ1 = ∑ i, algebraMap R k (c i) • OactH k B (b i) ξ0 := by
      refine Prod.ext ?_ ?_
      · simp only [hξ1def, hξ0def, Prod.fst_sum, Prod.smul_fst, OactH_eq, Matrix.sum_mulVec, Matrix.smul_mulVec]
      · simp only [hξ1def, hξ0def, Prod.snd_sum, Prod.smul_snd, OactH_eq, Matrix.sum_mulVec, Matrix.smul_mulVec]
    have hξ1 : ξ1 ∈ Hset (R := R) k h := by
      rw [hsum]
      exact hset_sum k h _ _ fun i _ => hset_smul k h (c i) (gauge_stable R d O k hRQ B h hc (b i) ξ0 hξ0)
    have hfirst : (∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U = U := by
      have he : ∀ i, (dActH k B (b i)).mulVec U = χ (ty ℓ') (b i) • U := fun i => heig ℓ' (b i)
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, he, smul_smul]
      rw [← Finset.sum_smul, hnorm, one_smul]
    obtain ⟨u1, φ1, hu1⟩ := hξ1
    have hU1 : (fun j => algebraMap R k (u1 j)) = U := by
      have h1 := congrArg Prod.fst hu1
      exact h1.symm.trans hfirst
    refine ⟨φ1, fun ℓ hℓ => ?_⟩
    obtain ⟨a, ha⟩ := hℓ
    obtain ⟨m, hb, hcm⟩ := hm (star a)
    have heigξ : OactH k B (star a) ξ1 = χ (ty ℓ') (star a) • ξ1 := by
      rw [OactH_eq]
      refine Prod.ext ?_ ?_
      · show (dActH k B (star a)).mulVec ((∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U) =
          χ (ty ℓ') (star a) • (∑ i, algebraMap R k (c i) • dActH k B (b i)).mulVec U
        rw [Matrix.mulVec_mulVec, idem_eig (dActH k B) (χ (ty ℓ')) b (fun i => algebraMap R k (c i)) (star a) m hb hcm,
          Matrix.smul_mulVec]
      · show (dActS k B (star a)).mulVec ((∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)) =
          χ (ty ℓ') (star a) • (∑ i, algebraMap R k (c i) • dActS k B (b i)).mulVec (-(sg1 k h).mulVec U)
        rw [Matrix.mulVec_mulVec, idem_eig (dActS k B) (χ (ty ℓ')) b (fun i => algebraMap R k (c i)) (star a) m hb hcm,
          Matrix.smul_mulVec]
    have hv : OactH k B a ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) =
        χ (ty ℓ) a • ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) := by
      rw [OactH_eq]
      refine Prod.ext ?_ ?_
      · exact heig ℓ a
      · simp
    have hs := beta_sesquilinear R d O k B a ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1
    rw [hv, heigξ, betaH_smul_left, betaH_smul_right] at hs
    have hβ : betaH k ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1 = 0 := by
      have h2 : (χ (ty ℓ) a - χ (ty ℓ') (star a)) * betaH k ((fun i => algebraMap R k (u ℓ i)), (0 : Fin d → k)) ξ1 = 0 := by
        rw [sub_mul, hs, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    rw [hu1] at hβ
    simp only [betaH, Pi.zero_apply, zero_mul, sub_zero] at hβ
    rw [hU1] at hβ
    exact hβ
  choose φ hφ using key
  exact ⟨φ, fun ℓ ℓ' hℓ => hφ ℓ' ℓ hℓ⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
