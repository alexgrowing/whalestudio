import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.OvF

section Mat
variable {k : Type} [Field k]

private theorem low_l {n : M4 k} (h : IsLow n) : adj n * n = 1 := by
  have h1 := h.1
  unfold IsGSp at h1
  simpa using h1

private theorem low_r {n : M4 k} (h : IsLow n) : n * adj n = 1 := mul_eq_one_comm.1 (low_l h)

end Mat

section Grp
variable {k Γ : Type} [Field k] [Group Γ]

end Grp

section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

variable {D : Raw Ω c} {T T' : Tower D} {hT : T.Le T'} {k : Type} [Field k] {a : c.O →+* k}

end Gal

end UpperTheory.V.Ws.OvF

private theorem eq_of_isLow_of_isUp_adj_mul_of_isUnit_det {k : Type} [Field k] {n m B : M4 k} (hn : IsLow n) (hm : IsLow m)
    (hB : IsUnit B.det) (h1 : IsUp (adj n * B)) (h2 : IsUp (adj m * B)) : n = m := by
  have hnr : n * adj n = 1 := UpperTheory.V.Ws.OvF.low_r hn
  have hmr : m * adj m = 1 := UpperTheory.V.Ws.OvF.low_r hm
  have hXu : IsUnit (adj n * B).det := by
    rw [Matrix.det_mul]
    exact IsUnit.mul (Matrix.isUnit_det_of_left_inverse hnr) hB
  have hC : adj m * n = (adj m * B) * (adj n * B)⁻¹ := by
    have e : adj m * B = (adj m * n) * (adj n * B) := by
      calc adj m * B = adj m * (n * adj n) * B := by rw [hnr, Matrix.mul_one]
        _ = (adj m * n) * (adj n * B) := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXu, Matrix.mul_one]
  have hCup : IsUp (adj m * n) := by
    rw [hC]
    have a1 : Matrix.BlockTriangular (adj m * B) id := fun i j hij => h2 i j hij
    have a2 : Matrix.BlockTriangular (adj n * B) id := fun i j hij => h1 i j hij
    haveI := Matrix.invertibleOfIsUnitDet _ hXu
    have a3 := a1.mul (Matrix.blockTriangular_inv_of_blockTriangular a2)
    exact fun i j hij => a3 hij
  have hC1 : adj m * n = 1 := by
    obtain ⟨-, hmd, hmz⟩ := hm
    obtain ⟨-, hnd, hnz⟩ := hn
    have m01 := hmz 0 1 (by decide)
    have m02 := hmz 0 2 (by decide)
    have m03 := hmz 0 3 (by decide)
    have m12 := hmz 1 2 (by decide)
    have m13 := hmz 1 3 (by decide)
    have m23 := hmz 2 3 (by decide)
    have n01 := hnz 0 1 (by decide)
    have n02 := hnz 0 2 (by decide)
    have n03 := hnz 0 3 (by decide)
    have n12 := hnz 1 2 (by decide)
    have n13 := hnz 1 3 (by decide)
    have n23 := hnz 2 3 (by decide)
    have m0 := hmd 0
    have m1 := hmd 1
    have m2 := hmd 2
    have m3 := hmd 3
    have d0 := hnd 0
    have d1 := hnd 1
    have d2 := hnd 2
    have d3 := hnd 3
    ext i j
    rcases lt_trichotomy j i with hij | hij | hij
    · rw [hCup i j hij]
      fin_cases i <;> fin_cases j <;> simp_all
    · subst hij
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, adj, sgn, Fin.rev, m01, m02, m03, m12, m13, m23,
        n01, n02, n03, n12, n13, n23, m0, m1, m2, m3, d0, d1, d2, d3]
    · fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) at hij ⊢ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, adj, sgn, Fin.rev, m01, m02, m03, m12, m13, m23,
          n01, n02, n03, n12, n13, n23, m0, m1, m2, m3, d0, d1, d2, d3]
  calc n = (m * adj m) * n := by rw [hmr, Matrix.one_mul]
    _ = m * (adj m * n) := Matrix.mul_assoc _ _ _
    _ = m := by rw [hC1, Matrix.mul_one]

private theorem inv_mul_mem_dec_of_both_map_place {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {A A' : ValuationSubring Ω}
    {g₁ g₂ : G F Ω} (h1 : ∀ x, g₁ x ∈ A' ↔ x ∈ A) (h2 : ∀ x, g₂ x ∈ A' ↔ x ∈ A) :
    g₁⁻¹ * g₂ ∈ Dec (F := F) A := by
  unfold Dec
  letI : MulAction (G F Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mul_inv_rev, inv_inv, AlgEquiv.smul_def, AlgEquiv.mul_apply]
  rw [← h2, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply, h1]

private theorem over_fact_of_isLow_of_flag {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [Algebra F Ω] [Algebra F' Ω]
    {φ : G F' Ω →* G F Ω} {ι ι' k : Type} [Field k] {pl : ι → ValuationSubring Ω}
    {pl' : ι' → ValuationSubring Ω} {P : PD ι (G F Ω) k} {P' : PD ι' (G F' Ω) k} (hO : Over φ pl pl' P P')
    (hlow : ∀ v, IsLow (P.n v)) (hflag : ∀ v, ∀ s ∈ Dec (F := F) (pl v), IsUp (adj (P.n v) * P.r s * P.n v))
    (hv : ∀ v' v₁ v₂ (g₁ g₂ : G F Ω), (∀ x, g₁ x ∈ pl' v' ↔ x ∈ pl v₁) → (∀ x, g₂ x ∈ pl' v' ↔ x ∈ pl v₂) → v₁ = v₂)
    (v' : ι') (v : ι) (g : G F Ω) (hg : ∀ x, g x ∈ pl' v' ↔ x ∈ pl v) :
    IsUp (adj (P'.n v') * P.r g * P.n v) := by
  unfold Over at hO
  obtain ⟨-, hOn⟩ := hO
  obtain ⟨v₂, g₂, hg₂, hup⟩ := hOn v'
  have hvv := hv v' v₂ v g₂ g hg₂ hg
  subst hvv
  have hU := hflag v₂ _ (inv_mul_mem_dec_of_both_map_place hg₂ hg)
  have e : adj (P'.n v') * P.r g * P.n v₂ =
      (adj (P'.n v') * P.r g₂ * P.n v₂) * (adj (P.n v₂) * P.r (g₂⁻¹ * g) * P.n v₂) := by
    rw [map_mul]
    calc adj (P'.n v') * P.r g * P.n v₂ = adj (P'.n v') * (P.r g₂ * P.r g₂⁻¹ * P.r g) * P.n v₂ := by
          rw [← map_mul, mul_inv_cancel, map_one, Matrix.one_mul]
      _ = adj (P'.n v') * P.r g₂ * (P.n v₂ * adj (P.n v₂)) * P.r g₂⁻¹ * P.r g * P.n v₂ := by
          rw [UpperTheory.V.Ws.OvF.low_r (hlow v₂)]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  have a1 : Matrix.BlockTriangular (adj (P'.n v') * P.r g₂ * P.n v₂) id := fun i j hij => hup i j hij
  have a2 : Matrix.BlockTriangular (adj (P.n v₂) * P.r (g₂⁻¹ * g) * P.n v₂) id := fun i j hij => hU i j hij
  exact fun i j hij => (a1.mul a2) hij

private theorem over_pd_unique_of_isLow_of_flag {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [Algebra F Ω] [Algebra F' Ω]
    {φ : G F' Ω →* G F Ω} {ι ι' k : Type} [Field k] {pl : ι → ValuationSubring Ω}
    {pl' : ι' → ValuationSubring Ω} {P : PD ι (G F Ω) k} {P' Q' : PD ι' (G F' Ω) k} (hO : Over φ pl pl' P P')
    (hQ : Over φ pl pl' P Q')
    (hlow : ∀ v, IsLow (P.n v)) (hflag : ∀ v, ∀ s ∈ Dec (F := F) (pl v), IsUp (adj (P.n v) * P.r s * P.n v))
    (hv : ∀ v' v₁ v₂ (g₁ g₂ : G F Ω), (∀ x, g₁ x ∈ pl' v' ↔ x ∈ pl v₁) → (∀ x, g₂ x ∈ pl' v' ↔ x ∈ pl v₂) → v₁ = v₂)
    (hl1 : ∀ v', IsLow (P'.n v')) (hl2 : ∀ v', IsLow (Q'.n v')) : P' = Q' := by
  have hQ' := hQ
  unfold Over at hO hQ
  obtain ⟨hOr, hOn⟩ := hO
  obtain ⟨hQr, -⟩ := hQ
  have hr : P'.r = Q'.r := hOr.trans hQr.symm
  have hn : P'.n = Q'.n := by
    funext v'
    obtain ⟨v, g, hg, hup⟩ := hOn v'
    have hup2 := over_fact_of_isLow_of_flag hQ' hlow hflag hv v' v g hg
    have hB : IsUnit (P.r g * P.n v).det := by
      apply Matrix.isUnit_det_of_right_inverse (B := adj (P.n v) * P.r g⁻¹)
      calc P.r g * P.n v * (adj (P.n v) * P.r g⁻¹) = P.r g * (P.n v * adj (P.n v)) * P.r g⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [UpperTheory.V.Ws.OvF.low_r (hlow v), Matrix.mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply eq_of_isLow_of_isUp_adj_mul_of_isUnit_det (hl1 v') (hl2 v') hB
    · simpa only [Matrix.mul_assoc] using hup
    · simpa only [Matrix.mul_assoc] using hup2
  cases P'
  cases Q'
  simp only at hr hn
  subst hr
  subst hn
  rfl

private theorem over_comp_of_over_of_isLow {Ω F F' F'' : Type} [Field Ω] [Field F] [Field F'] [Field F''] [Algebra F Ω]
    [Algebra F' Ω] [Algebra F'' Ω] {φ : G F' Ω →* G F Ω} {ψ : G F'' Ω →* G F' Ω} (hφ : ∀ g x, φ g x = g x)
    {ι ι' ι'' k : Type} [Field k] {pl : ι → ValuationSubring Ω} {pl' : ι' → ValuationSubring Ω}
    {pl'' : ι'' → ValuationSubring Ω} {P : PD ι (G F Ω) k} {P' : PD ι' (G F' Ω) k} {P'' : PD ι'' (G F'' Ω) k}
    (h1 : Over φ pl pl' P P') (h2 : Over ψ pl' pl'' P' P'') (hl : ∀ v', IsLow (P'.n v')) :
    Over (φ.comp ψ) pl pl'' P P'' := by
  unfold Over at h1 h2 ⊢
  obtain ⟨h1r, h1n⟩ := h1
  obtain ⟨h2r, h2n⟩ := h2
  refine ⟨by rw [h2r, h1r]; rfl, fun v'' => ?_⟩
  obtain ⟨v', g', hg', hu'⟩ := h2n v''
  obtain ⟨v, g, hg, hu⟩ := h1n v'
  refine ⟨v, φ g' * g, fun x => ?_, ?_⟩
  · rw [AlgEquiv.mul_apply, hφ, hg', hg]
  · have e1 : P'.r g' = P.r (φ g') := by rw [h1r]; rfl
    have e : adj (P''.n v'') * P.r (φ g' * g) * P.n v =
        (adj (P''.n v'') * P'.r g' * P'.n v') * (adj (P'.n v') * P.r g * P.n v) := by
      rw [e1, map_mul]
      calc adj (P''.n v'') * (P.r (φ g') * P.r g) * P.n v =
            adj (P''.n v'') * P.r (φ g') * (P'.n v' * adj (P'.n v')) * P.r g * P.n v := by
            rw [UpperTheory.V.Ws.OvF.low_r (hl v')]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    have a1 : Matrix.BlockTriangular (adj (P''.n v'') * P'.r g' * P'.n v') id := fun i j hij => hu' i j hij
    have a2 : Matrix.BlockTriangular (adj (P'.n v') * P.r g * P.n v) id := fun i j hij => hu i j hij
    exact fun i j hij => (a1.mul a2) hij

private theorem first_column_and_entry_two_one_of_isUp_adj_mul {k : Type} [Field k] {n M : M4 k} (hn : IsLow n) (h : IsUp (adj n * M)) :
    (∀ i, n i 0 * M 0 0 = M i 0) ∧ (M 0 1 = 0 → M 2 1 = 0 → M 1 1 ≠ 0 → n 2 1 = 0) := by
  obtain ⟨X, hXd⟩ : ∃ X, X = adj n * M := ⟨_, rfl⟩
  have hM : M = n * X := by rw [hXd, ← Matrix.mul_assoc, UpperTheory.V.Ws.OvF.low_r hn, Matrix.one_mul]
  rw [← hXd] at h
  obtain ⟨-, hd, hz⟩ := hn
  have n01 := hz 0 1 (by decide)
  have n02 := hz 0 2 (by decide)
  have n03 := hz 0 3 (by decide)
  have n12 := hz 1 2 (by decide)
  have n13 := hz 1 3 (by decide)
  have n23 := hz 2 3 (by decide)
  have x10 := h 1 0 (by decide)
  have x20 := h 2 0 (by decide)
  have x30 := h 3 0 (by decide)
  have x21 := h 2 1 (by decide)
  have x31 := h 3 1 (by decide)
  have x32 := h 3 2 (by decide)
  have d0 := hd 0
  subst hM
  constructor
  · intro i
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_four, n01, n02, n03, n12, n13, n23, x10, x20, x30,
      x21, x31, x32, d0]
  · intro h01 h21 h11
    simp [Matrix.mul_apply, Fin.sum_univ_four, n01, n02, n03, n12, n13, n23, x10, x20, x30,
      x21, x31, x32, d0] at h01 h21 h11
    rw [h01] at h21 h11
    simp [hd 1] at h21 h11
    tauto

private theorem entry_pow_mul_sub_eq_and_diag_pow {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (i j : Fin 4) (hij : i ≠ j)
    (hc : ∀ x y, r (x * y) i j = r x i j * r y j j + r x i i * r y i j)
    (hdi : ∀ x y, r (x * y) i i = r x i i * r y i i) (hdj : ∀ x y, r (x * y) j j = r x j j * r y j j)
    (x : Γ) (m : ℕ) : r (x ^ m) i j * (r x i i - r x j j) = r x i j * (r x i i ^ m - r x j j ^ m) ∧
      r (x ^ m) i i = r x i i ^ m ∧ r (x ^ m) j j = r x j j ^ m := by
  induction m with
  | zero => simp [Matrix.one_apply, hij]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [pow_succ, hc, hdi, hdj, h2, h3]
    refine ⟨?_, by ring, by ring⟩
    linear_combination (r x j j) * h1

private theorem exists_entry_pow_l_pow_ne_zero {Γ k : Type} [Group Γ] [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (r : Γ →* M4 k) (i j : Fin 4) (hij : i ≠ j)
    (hc : ∀ x y, r (x * y) i j = r x i j * r y j j + r x i i * r y i j)
    (hdi : ∀ x y, r (x * y) i i = r x i i * r y i i) (hdj : ∀ x y, r (x * y) j j = r x j j * r y j j)
    (hd : ∀ x (q : Fin 4), r x q q ≠ 0) (x y : Γ) (hx : r x i j ≠ 0) (hy : r y i i ≠ r y j j) :
    ∃ z, ∀ e : ℕ, r (z ^ (l ^ e)) i j ≠ 0 := by
  have key : ∀ z, r z i j ≠ 0 → r z i i ≠ r z j j → ∀ e : ℕ, r (z ^ (l ^ e)) i j ≠ 0 := by
    intro z hz hz' e h0
    have h1 := (entry_pow_mul_sub_eq_and_diag_pow r i j hij hc hdi hdj z (l ^ e)).1
    rw [h0, zero_mul, ← sub_pow_char_pow] at h1
    exact (mul_ne_zero hz (pow_ne_zero _ (sub_ne_zero.2 hz'))) h1.symm
  by_cases h1 : r x i i = r x j j
  · by_cases h2 : r y i j = 0
    · refine ⟨y * x, key _ ?_ ?_⟩
      · rw [hc, h2, zero_mul, zero_add]
        exact mul_ne_zero (hd y i) hx
      · rw [hdi, hdj, h1]
        intro h
        exact hy (mul_right_cancel₀ (hd x j) h)
    · exact ⟨y, key y h2 hy⟩
  · exact ⟨x, key x hx h1⟩

private theorem residue_mul_inv_eq_one_of_map_eq {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k) (u v : Oˣ)
    (h : a u = a v) : IsLocalRing.residue O ↑(u * v⁻¹) = 1 := by
  have hm : (u : O) - v ∈ IsLocalRing.maximalIdeal O := by
    by_contra hn
    have hu := (IsLocalRing.notMem_maximalIdeal.1 hn).map a
    rw [map_sub, h, sub_self] at hu
    exact not_isUnit_zero hu
  have e : IsLocalRing.residue O u = IsLocalRing.residue O v := Ideal.Quotient.eq.2 hm
  rw [Units.val_mul, map_mul, e, ← map_mul, Units.mul_inv, map_one]

private theorem charP_of_ringHom_kills_maxIdeal {l : ℕ} [Fact l.Prime] (c : Coef l) {k : Type} [Field k] (a : c.O →+* k)
    (ha : ∀ x ∈ IsLocalRing.maximalIdeal c.O, a x = 0) : CharP k l := by
  haveI := c.dvr
  haveI := c.fin
  have hl : ((l : ℕ) : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hinj : Function.Injective (algebraMap ℤ_[l] c.O) := by
      intro x y hxy
      have h2 := congrArg (fun z : c.O => (z : PadicAlgCl l)) hxy
      have h3 : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
        rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])
      exact h3 (by simpa using h2)
    haveI : FaithfulSMul ℤ_[l] c.O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have h4 : IsUnit (algebraMap ℤ_[l] c.O (l : ℤ_[l])) := by simpa using hu
    exact PadicInt.p_nonunit ((isUnit_map_iff (algebraMap ℤ_[l] c.O) _).mp h4)
  rw [CharP.charP_iff_prime_eq_zero (Fact.out)]
  have := ha _ hl
  simpa using this

private theorem exists_pow_res_surj_of_tower_le {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} {T T' : Tower D} (hT : T.Le T') :
    ∃ e : ℕ, ∀ z : G T.F Ω, ∃ h : G T'.F Ω, resLe hT.le h = z ^ (l ^ e) := by
  obtain ⟨e, he⟩ := hT.pow
  refine ⟨e, fun z => ?_⟩
  have hz : resQ T.F z ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact z.commutes ⟨x, hx⟩
  have h2 := he _ hz
  refine ⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, h2⟩, ?_⟩
  apply AlgEquiv.ext
  intro x
  show ((resQ T.F z) ^ l ^ e) x = (z ^ l ^ e) x
  rw [← map_pow]
  rfl

private theorem diag_product_eq_of_isGSp_of_entries_zero {k : Type} [Field k] {X : M4 k} {ν : k} (h : IsGSp ν X) (z01 : X 0 1 = 0)
    (z02 : X 0 2 = 0) (z03 : X 0 3 = 0) (z13 : X 1 3 = 0) (z23 : X 2 3 = 0) (z12 : X 1 2 * X 2 1 = 0) :
    X 0 0 * X 3 3 = X 1 1 * X 2 2 := by
  unfold IsGSp at h
  have e0 := congrFun (congrFun h 0) 0
  have e1 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj, sgn, Fin.rev, z01, z02, z03, z13, z23] at e0 e1
  linear_combination e0 - e1 - z12

private theorem exists_entry_ne_zero_of_triangular_mul {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (φ : Γ' →* Γ) (r : Γ →* M4 k) (r' : Γ' →* M4 k) (hr : ∀ g, r' g = r (φ g))
    (hlift : ∃ e : ℕ, ∀ z, ∃ h, φ h = z ^ (l ^ e)) (i j : Fin 4) (hij : i ≠ j)
    (hc : ∀ x y, r (x * y) i j = r x i j * r y j j + r x i i * r y i j)
    (hdi : ∀ x y, r (x * y) i i = r x i i * r y i i) (hdj : ∀ x y, r (x * y) j j = r x j j * r y j j)
    (hd : ∀ x (q : Fin 4), r x q q ≠ 0) (x y : Γ) (hx : r x i j ≠ 0) (hy : r y i i ≠ r y j j) :
    ∃ h, r' h i j ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_entry_pow_l_pow_ne_zero l r i j hij hc hdi hdj hd x y hx hy
  obtain ⟨e, he⟩ := hlift
  obtain ⟨h, hh⟩ := he z
  exact ⟨h, by rw [hr, hh]; exact hz e⟩

private theorem mul_inv_mul_mul_inv_eq {Γ : Type} [CommGroup Γ] (a b c : Γ) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  rw [mul_comm c, ← mul_assoc, mul_assoc a, mul_comm b⁻¹ a⁻¹, ← mul_assoc, mul_inv_cancel, one_mul, mul_comm]

set_option maxHeartbeats 1000000 in
open UpperTheory.V.Ws.OvF in
theorem UpperTheory.V.Ws.overFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T T' : Tower D) (hT : T.Le T'), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ (W W' : Finset ℕ) (s t : PD T.ι (G T.F Ω) k) (s' t' : PD T'.ι (G T'.F Ω) k),
      (T.fr W).IsRes a s → (T.fr W).IsRes a t → (T'.fr W').IsRes a s' → (T'.fr W').IsRes a t' → T.OverT hT s s' → T.OverT hT t t' →
      (s = t → s' = t') ∧ (∀ S, Supp S s.r → Supp S s'.r) ∧ (s.In nP → s'.In nP) ∧ (s.In nP → t.In nP → s.SamePs t → s'.SamePs t') ∧
        (Supp nM s.r → Supp nM t.r → s.SameAl t → s'.SameAl t') ∧ (Supp nP s.r → Ent s.r (-wPs) → Ent s'.r (-wPs)) ∧
        (Supp nM s.r → (Ent s.r (-wAl) → Ent s'.r (-wAl)) ∧ (Ent s.r (-wBe) → Ent s'.r (-wBe))) ∧
        ∀ (s₀ : PD Unit (G ℚ Ω) k) (g0 : G ℚ Ω), (frQ D T.pr g0).IsPair a s₀ → T.OverQ s₀ s → ∀ u, (T'.fr W').IsRes a u → T'.OverQ s₀ u → u = s' := by
  intro Ω _ _ _ l _ c D hD T T' hT hF k _ a ha W W' s t s' t' hs ht hs' ht' hss' htt'
  haveI := charP_of_ringHom_kills_maxIdeal c a ha
  have hvT : ∀ (v' : T'.ι) (v₁ v₂ : T.ι) (g₁ g₂ : G T.F Ω), (∀ x, g₁ x ∈ T'.pl v' ↔ x ∈ T.pl v₁) →
      (∀ x, g₂ x ∈ T'.pl v' ↔ x ∈ T.pl v₂) → v₁ = v₂ := by
    intro v' v₁ v₂ g₁ g₂ h1 h2
    obtain ⟨v, -, hu⟩ := T.cover (T'.pl v') (T'.ovl v')
    exact (hu v₁ ⟨g₁, h1⟩).trans (hu v₂ ⟨g₂, h2⟩).symm
  have hO1 : Over (resLe hT.le) T.pl T'.pl s s' := hss'
  have hO2 : Over (resLe hT.le) T.pl T'.pl t t' := htt'
  unfold Over at hO1 hO2
  have hsr : ∀ g, s'.r g = s.r (resLe hT.le g) := fun g => by rw [hO1.1]; rfl
  have htr : ∀ g, t'.r g = t.r (resLe hT.le g) := fun g => by rw [hO2.1]; rfl
  have hunit : ∀ u : (↥c.O)ˣ, a u ≠ 0 := fun u => (u.isUnit.map a).ne_zero
  have hds := hs.res.diag
  have hdt := ht.res.diag
  have hlift := exists_pow_res_surj_of_tower_le hT
  have hdm : ∀ x y (q : Fin 4), s.r (x * y) q q = s.r x q q * s.r y q q := by
    intro x y q
    rw [hds, hds, hds, map_mul, Units.val_mul, map_mul]
  have hd0 : ∀ x (q : Fin 4), s.r x q q ≠ 0 := fun x q => by rw [hds]; exact hunit _
  have hok := hF.1
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8⟩
  case c1 =>
    intro hst
    subst hst
    exact over_pd_unique_of_isLow_of_flag hss' htt' hs.pair.low hs.pair.flag hvT hs'.pair.low ht'.pair.low
  case c2 =>
    intro S hS g
    rw [hsr]
    exact hS _
  case c3 =>
    rintro ⟨hS, hN⟩
    refine ⟨fun g => by rw [hsr]; exact hS _, fun v' => ?_⟩
    obtain ⟨v, g, hg, hup⟩ := hO1.2 v'
    have hlow' := hs'.pair.low v'
    have hl := hs.pair.low v
    have h6 := (first_column_and_entry_two_one_of_isUp_adj_mul hlow' (M := s.r g * s.n v) (by simpa only [Matrix.mul_assoc] using hup)).2
    have r01 := hS g 0 1 (by decide) (by decide)
    have r02 := hS g 0 2 (by decide) (by decide)
    have r03 := hS g 0 3 (by decide) (by decide)
    have r13 := hS g 1 3 (by decide) (by decide)
    have r23 := hS g 2 3 (by decide) (by decide)
    have r21 := hS g 2 1 (by decide) (by decide)
    have n21 := hN v 2 1 (by decide) (by decide)
    have n01 := hl.2.2 0 1 (by decide)
    have n11 := hl.2.1 1
    have h21 : s'.n v' 2 1 = 0 := h6
      (by simp [Matrix.mul_apply, Fin.sum_univ_four, r01, r02, r03, n01, n21])
      (by simp [Matrix.mul_apply, Fin.sum_univ_four, r21, r23, n01, n21])
      (by simpa [Matrix.mul_apply, Fin.sum_univ_four, r13, n01, n21, n11] using hd0 g 1)
    unfold SuppM
    intro i j hij hw
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact absurd (by decide) hw
      | exact hlow'.2.2 _ _ (by decide)
      | exact h21
  case c4 =>
    rintro ⟨hS, hN⟩ ⟨hSt, hNt⟩ ⟨hr, hn⟩
    refine ⟨fun g => by rw [hsr, htr]; exact hr _, fun v' => ?_⟩
    obtain ⟨v, g, hg, hup⟩ := hO1.2 v'
    have hup2 := over_fact_of_isLow_of_flag htt' ht.pair.low ht.pair.flag hvT v' v g hg
    have e1 := (first_column_and_entry_two_one_of_isUp_adj_mul (hs'.pair.low v') (M := s.r g * s.n v) (by simpa only [Matrix.mul_assoc] using hup)).1 2
    have e2 := (first_column_and_entry_two_one_of_isUp_adj_mul (ht'.pair.low v') (M := t.r g * t.n v) (by simpa only [Matrix.mul_assoc] using hup2)).1 2
    have n00 := (hs.pair.low v).2.1 0
    have m00 := (ht.pair.low v).2.1 0
    have r01 := hS g 0 1 (by decide) (by decide)
    have r02 := hS g 0 2 (by decide) (by decide)
    have r03 := hS g 0 3 (by decide) (by decide)
    have r21 := hS g 2 1 (by decide) (by decide)
    have r23 := hS g 2 3 (by decide) (by decide)
    have q01 := hSt g 0 1 (by decide) (by decide)
    have q02 := hSt g 0 2 (by decide) (by decide)
    have q03 := hSt g 0 3 (by decide) (by decide)
    have q21 := hSt g 2 1 (by decide) (by decide)
    have q23 := hSt g 2 3 (by decide) (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_four, n00, m00, r01, r02, r03, r21, r23, q01, q02, q03, q21, q23,
      mul_zero, zero_mul, add_zero, zero_add, mul_one] at e1 e2
    have d00 : t.r g 0 0 = s.r g 0 0 := by rw [hds, hdt]
    have d22 : t.r g 2 2 = s.r g 2 2 := by rw [hds, hdt]
    rw [d00, d22, ← hr g, ← hn v] at e2
    apply mul_right_cancel₀ (hd0 g 0)
    linear_combination e1 - e2
  case c5 =>
    intro hS hSt ⟨hr, hn⟩
    refine ⟨fun g => by rw [hsr, htr]; exact hr _, fun v' => ?_⟩
    obtain ⟨v, g, hg, hup⟩ := hO1.2 v'
    have hup2 := over_fact_of_isLow_of_flag htt' ht.pair.low ht.pair.flag hvT v' v g hg
    have e1 := (first_column_and_entry_two_one_of_isUp_adj_mul (hs'.pair.low v') (M := s.r g * s.n v) (by simpa only [Matrix.mul_assoc] using hup)).1 1
    have e2 := (first_column_and_entry_two_one_of_isUp_adj_mul (ht'.pair.low v') (M := t.r g * t.n v) (by simpa only [Matrix.mul_assoc] using hup2)).1 1
    have n00 := (hs.pair.low v).2.1 0
    have m00 := (ht.pair.low v).2.1 0
    have r01 := hS g 0 1 (by decide) (by decide)
    have r02 := hS g 0 2 (by decide) (by decide)
    have r03 := hS g 0 3 (by decide) (by decide)
    have r12 := hS g 1 2 (by decide) (by decide)
    have r13 := hS g 1 3 (by decide) (by decide)
    have q01 := hSt g 0 1 (by decide) (by decide)
    have q02 := hSt g 0 2 (by decide) (by decide)
    have q03 := hSt g 0 3 (by decide) (by decide)
    have q12 := hSt g 1 2 (by decide) (by decide)
    have q13 := hSt g 1 3 (by decide) (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_four, n00, m00, r01, r02, r03, r12, r13, q01, q02, q03, q12, q13,
      mul_zero, zero_mul, add_zero, zero_add, mul_one] at e1 e2
    have d00 : t.r g 0 0 = s.r g 0 0 := by rw [hds, hdt]
    have d11 : t.r g 1 1 = s.r g 1 1 := by rw [hds, hdt]
    rw [d00, d11, ← hr g, ← hn v] at e2
    apply mul_right_cancel₀ (hd0 g 0)
    linear_combination e1 - e2
  case c6 =>
    unfold Ent
    rintro hS ⟨g, i, j, hw, hne⟩
    obtain ⟨y, -, hy⟩ := hok.g3 (-wPs) (by decide)
    have hne02 : s.r y 2 2 ≠ s.r y 0 0 := by
      rw [hds, hds]
      intro h
      apply hy
      have e : (T.fr ∅).rt (-wPs) y = (T.fr W).χ 2 y * ((T.fr W).χ 0 y)⁻¹ := by
        simp [Fr.rt, wPs, Tower.fr]
      rw [Tower.rb, e]
      exact residue_mul_inv_eq_one_of_map_eq a _ _ h
    have hrel : s.r y 0 0 * s.r y 3 3 = s.r y 1 1 * s.r y 2 2 :=
      diag_product_eq_of_isGSp_of_entries_zero (hs.pair.mult y) (hS y 0 1 (by decide) (by decide)) (hS y 0 2 (by decide) (by decide))
        (hS y 0 3 (by decide) (by decide)) (hS y 1 3 (by decide) (by decide)) (hS y 2 3 (by decide) (by decide))
        (by rw [hS y 2 1 (by decide) (by decide), mul_zero])
    fin_cases i <;> fin_cases j <;> (try exact absurd hw (by decide))
    · obtain ⟨h, hh⟩ := exists_entry_ne_zero_of_triangular_mul l (resLe hT.le) s.r s'.r hsr hlift 2 0 (by decide)
        (fun x z => by
          rw [map_mul]
          simp [Matrix.mul_apply, Fin.sum_univ_four, hS x 2 1 (by decide) (by decide),
            hS x 2 3 (by decide) (by decide)])
        (fun x z => hdm x z 2) (fun x z => hdm x z 0) hd0 g y hne hne02
      exact ⟨h, 2, 0, by decide, hh⟩
    · have hne13 : s.r y 3 3 ≠ s.r y 1 1 := by
        intro h
        apply hne02
        rw [h] at hrel
        apply mul_left_cancel₀ (hd0 y 1)
        linear_combination -hrel
      obtain ⟨h, hh⟩ := exists_entry_ne_zero_of_triangular_mul l (resLe hT.le) s.r s'.r hsr hlift 3 1 (by decide)
        (fun x z => by
          rw [map_mul]
          simp [Matrix.mul_apply, Fin.sum_univ_four, hS z 0 1 (by decide) (by decide),
            hS z 2 1 (by decide) (by decide)])
        (fun x z => hdm x z 3) (fun x z => hdm x z 1) hd0 g y hne hne13
      exact ⟨h, 3, 1, by decide, hh⟩
  case c7 =>
    unfold Ent
    intro hS
    obtain ⟨y, -, hy⟩ := hok.g3 (-wAl) (by decide)
    obtain ⟨y2, -, hy2⟩ := hok.g3 (-wBe) (by decide)
    have hne10 : s.r y 1 1 ≠ s.r y 0 0 := by
      rw [hds, hds]
      intro h
      apply hy
      have e : (T.fr ∅).rt (-wAl) y = (T.fr W).χ 1 y * ((T.fr W).χ 0 y)⁻¹ := by
        simp [Fr.rt, wAl, Tower.fr]
      rw [Tower.rb, e]
      exact residue_mul_inv_eq_one_of_map_eq a _ _ h
    have hne21 : s.r y2 2 2 ≠ s.r y2 1 1 := by
      rw [hds, hds]
      intro h
      apply hy2
      have e : (T.fr ∅).rt (-wBe) y2 = (T.fr W).χ 2 y2 * ((T.fr W).χ 1 y2)⁻¹ := by
        simp [Fr.rt, wBe, Tower.fr]
        exact mul_inv_mul_mul_inv_eq _ _ _
      rw [Tower.rb, e]
      exact residue_mul_inv_eq_one_of_map_eq a _ _ h
    have hrel : s.r y 0 0 * s.r y 3 3 = s.r y 1 1 * s.r y 2 2 :=
      diag_product_eq_of_isGSp_of_entries_zero (hs.pair.mult y) (hS y 0 1 (by decide) (by decide)) (hS y 0 2 (by decide) (by decide))
        (hS y 0 3 (by decide) (by decide)) (hS y 1 3 (by decide) (by decide)) (hS y 2 3 (by decide) (by decide))
        (by rw [hS y 1 2 (by decide) (by decide), zero_mul])
    constructor
    · rintro ⟨g, i, j, hw, hne⟩
      fin_cases i <;> fin_cases j <;> (try exact absurd hw (by decide))
      · obtain ⟨h, hh⟩ := exists_entry_ne_zero_of_triangular_mul l (resLe hT.le) s.r s'.r hsr hlift 1 0 (by decide)
          (fun x z => by
            rw [map_mul]
            simp [Matrix.mul_apply, Fin.sum_univ_four, hS x 1 2 (by decide) (by decide),
              hS x 1 3 (by decide) (by decide)])
          (fun x z => hdm x z 1) (fun x z => hdm x z 0) hd0 g y hne hne10
        exact ⟨h, 1, 0, by decide, hh⟩
      · have hne32 : s.r y 3 3 ≠ s.r y 2 2 := by
          intro h
          apply hne10
          rw [h] at hrel
          apply mul_right_cancel₀ (hd0 y 2)
          linear_combination -hrel
        obtain ⟨h, hh⟩ := exists_entry_ne_zero_of_triangular_mul l (resLe hT.le) s.r s'.r hsr hlift 3 2 (by decide)
          (fun x z => by
            rw [map_mul]
            simp [Matrix.mul_apply, Fin.sum_univ_four, hS z 0 2 (by decide) (by decide),
              hS z 1 2 (by decide) (by decide)])
          (fun x z => hdm x z 3) (fun x z => hdm x z 2) hd0 g y hne hne32
        exact ⟨h, 3, 2, by decide, hh⟩
    · rintro ⟨g, i, j, hw, hne⟩
      fin_cases i <;> fin_cases j <;> (try exact absurd hw (by decide))
      obtain ⟨h, hh⟩ := exists_entry_ne_zero_of_triangular_mul l (resLe hT.le) s.r s'.r hsr hlift 2 1 (by decide)
        (fun x z => by
          rw [map_mul]
          simp [Matrix.mul_apply, Fin.sum_univ_four, hS z 0 1 (by decide) (by decide),
            hS x 2 3 (by decide) (by decide)])
        (fun x z => hdm x z 2) (fun x z => hdm x z 1) hd0 g y2 hne hne21
      exact ⟨h, 2, 1, by decide, hh⟩
  case c8 =>
    intro s₀ g0 hs0 hs0s u hu hus0
    have hc : Over ((resQ T.F).comp (resLe hT.le)) (fun _ => D.pl l) T'.pl s₀ s' :=
      over_comp_of_over_of_isLow (fun _ _ => rfl) hs0s hss' hs.pair.low
    have e : (resQ T.F).comp (resLe hT.le) = resQ T'.F := by
      ext g x
      rfl
    rw [e] at hc
    exact over_pd_unique_of_isLow_of_flag hus0 hc hs0.low hs0.flag (fun _ _ _ _ _ _ _ => Subsingleton.elim _ _) hu.pair.low hs'.pair.low
