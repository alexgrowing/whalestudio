import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem co_sqrt {O C : Type} [CommRing O] [IsLocalRing O] [CommRing C] [Algebra O C] [IsCO O C]
    (h2 : IsUnit (2 : C)) (a : C) (z : ResidueField O) (hz : z ≠ 0) (ha : res O C a = z ^ 2) :
    ∃ ζ : C, res O C ζ = z ∧ ζ ^ 2 = a := by
  haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  set ζ₀ := algebraMap O C b
  have hr : res O C ζ₀ = residue O b := (res O C).commutes b
  have hu : IsUnit ζ₀ := by
    by_contra hc
    exact hz (hr ▸ (res_eq_zero_iff O C ζ₀).2 ((IsLocalRing.mem_maximalIdeal _).2 hc))
  set u := hu.unit
  have hinv : res O C (↑u⁻¹ : C) * residue O b = 1 := by
    rw [← hr, ← map_mul]
    have : (↑u⁻¹ : C) * ζ₀ = 1 := by
      have := u.inv_mul
      simpa [u] using this
    rw [this, map_one]
  obtain ⟨α, hα, hα1⟩ := UpperTheory.V.AlgebraTools.sqrt_one_add (maximalIdeal C) (a * (↑u⁻¹ : C) ^ 2) h2 (by
    rw [← res_eq_zero_iff O, map_sub, map_mul, map_pow, ha, map_one]
    linear_combination (residue O b * res O C (↑u⁻¹ : C) + 1) * hinv)
  refine ⟨ζ₀ * α, ?_, ?_⟩
  · have h1 : res O C (α : C) = 1 := by
      have := (res_eq_zero_iff O C _).2 hα1
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    rw [map_mul, hr, h1, mul_one]
  · have hz0 : ζ₀ * (↑u⁻¹ : C) = 1 := by
      have := u.mul_inv
      simpa [u] using this
    calc (ζ₀ * α) ^ 2 = ζ₀ ^ 2 * (α : C) ^ 2 := by ring
      _ = ζ₀ ^ 2 * (a * (↑u⁻¹ : C) ^ 2) := by rw [hα]
      _ = a * (ζ₀ * (↑u⁻¹ : C)) ^ 2 := by ring
      _ = a := by rw [hz0, one_pow, mul_one]

private theorem skew_eig {K : Type} [Field K] {n : ℕ} (hn : n = 2 ∨ n = 3) (h2 : (2 : K) ≠ 0)
    (Q D : Matrix (Fin n) (Fin n) K) (ζ : K) (hQ : IsUnit Q) (hD : Dᵀ * Q = -(Q * D))
    (ht : (D * D).trace = 2 * ζ ^ 2) (i : Fin n) : ∃ v : Fin n → K, v ≠ 0 ∧ D *ᵥ v = ((w n i : K) * ζ) • v := by
  have hQ' : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have htr : D.trace = 0 := by
    have e : Dᵀ = -(Q * D) * Q⁻¹ := by
      rw [← hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
    have h : Dᵀ.trace = - D.trace := by
      rw [e, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hQ', Matrix.one_mul]
    rw [Matrix.trace_transpose] at h
    have : 2 * D.trace = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2
  suffices hdet : (((w n i : K) * ζ) • (1 : Matrix (Fin n) (Fin n) K) - D).det = 0 by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  rcases hn with rfl | rfl
  · have hf : ∀ (M : Matrix (Fin 2) (Fin 2) K) (x : K),
        2 * (x • (1 : Matrix (Fin 2) (Fin 2) K) - M).det = 2 * x ^ 2 - 2 * M.trace * x + M.trace ^ 2 - (M * M).trace := by
      intro M x
      simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h := hf D ((w 2 i : K) * ζ)
    rw [htr, ht] at h
    have hw : (w 2 i : K) ^ 2 = 1 := by
      fin_cases i <;> norm_num [UpperTheory.V.Fr.w]
    have : 2 * (((w 2 i : K) * ζ) • (1 : Matrix (Fin 2) (Fin 2) K) - D).det = 0 := by
      rw [h]
      linear_combination (2 * ζ ^ 2) * hw
    exact (mul_eq_zero.1 this).resolve_left h2
  · have hf : ∀ (M : Matrix (Fin 3) (Fin 3) K) (x : K),
        2 * (x • (1 : Matrix (Fin 3) (Fin 3) K) - M).det = 2 * x ^ 3 - 2 * M.trace * x ^ 2 + (M.trace ^ 2 - (M * M).trace) * x - 2 * M.det := by
      intro M x
      simp [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    have hdD : D.det = 0 := by
      have h := congrArg Matrix.det hD
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_neg, Matrix.det_mul] at h
      simp at h
      have : 2 * (D.det * Q.det) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' h2
      · exact (mul_eq_zero.1 h').resolve_right hQ'.ne_zero
    have h := hf D ((w 3 i : K) * ζ)
    rw [htr, ht, hdD] at h
    have hw : (w 3 i : K) ^ 3 = (w 3 i : K) := by
      fin_cases i <;> norm_num [UpperTheory.V.Fr.w]
    have : 2 * (((w 3 i : K) * ζ) • (1 : Matrix (Fin 3) (Fin 3) K) - D).det = 0 := by
      rw [h]
      linear_combination (2 * ζ ^ 3) * hw
    exact (mul_eq_zero.1 this).resolve_left h2

private theorem skew_norm {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (hn : n = 2 ∨ n = 3) (h2 : (2 : K) ≠ 0)
    (Q D : Matrix (Fin n) (Fin n) K) (ζ : K) (hζ : ζ ≠ 0) (hQ : IsUnit Q) (hs : Qᵀ = Q) (hD : Dᵀ * Q = -(Q * D))
    (hv : ∀ i : Fin n, ∃ v : Fin n → K, v ≠ 0 ∧ D *ᵥ v = ((w n i : K) * ζ) • v) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ Pᵀ * Q * P = Jmat K n ∧
      D * P = P * Matrix.diagonal fun i => (w n i : K) * ζ := by
  have h2ζ : (2 : K) * ζ ≠ 0 := mul_ne_zero h2 hζ
  have hμinj : Function.Injective (fun i : Fin n => (w n i : K) * ζ) := by
    intro i j h
    simp only at h
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;>
      first
      | exact hζ h
      | exact hζ h.symm
      | exact h2ζ (by linear_combination h)
      | exact h2ζ (by linear_combination -h)
  have hμsum : ∀ i j : Fin n, (w n i : K) * ζ + (w n j : K) * ζ = 0 → j = i.rev := by
    intro i j h
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;>
      first
      | exact hζ h
      | exact hζ h.symm
      | exact h2ζ (by linear_combination h)
      | exact h2ζ (by linear_combination -h)
  choose v hv0 hv using hv
  set μ : Fin n → K := fun i => (w n i : K) * ζ with hμ
  set V : Matrix (Fin n) (Fin n) K := Matrix.of fun a i => v i a with hVdef
  have hV : IsUnit V := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : V.col = v := by
      funext i a
      rfl
    rw [this]
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' D) μ hμinj v fun i => ?_
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hv i
  have hDV : D * V = V * Matrix.diagonal μ := by
    ext a i
    have := congrFun (hv i) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hVdef, Matrix.of_apply]
    rw [this, hμ, mul_comm]
  set M := Vᵀ * Q * V with hMdef
  have hMsym : ∀ i j, M j i = M i j := by
    intro i j
    have : Mᵀ = M := by
      rw [hMdef, Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.transpose_apply M i j, this]
  have hMu : IsUnit M := ((Matrix.isUnit_transpose V).2 hV |>.mul hQ).mul hV
  have hcomm : Matrix.diagonal μ * M = -(M * Matrix.diagonal μ) := by
    calc Matrix.diagonal μ * M = (V * Matrix.diagonal μ)ᵀ * Q * V := by
          rw [Matrix.transpose_mul, Matrix.diagonal_transpose, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Vᵀ * (Dᵀ * Q) * V := by
          rw [← hDV, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = -(M * Matrix.diagonal μ) := by
          rw [hD, Matrix.mul_neg, Matrix.neg_mul, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc]
  have hM0 : ∀ i j, j ≠ i.rev → M i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hcomm i) j
    simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal] at this
    have h' : (μ i + μ j) * M i j = 0 := by linear_combination this
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd (hμsum i j h) hij
    · exact h
  have hMr : ∀ i, M i i.rev ≠ 0 := by
    intro i h
    have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i fun j => by
      by_cases hj : j = i.rev
      · rw [hj]
        exact h
      · exact hM0 i j hj
    exact ((Matrix.isUnit_iff_isUnit_det M).1 hMu).ne_zero hdet
  obtain ⟨c, hc0, hc⟩ : ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧ ∀ i, c i * c i.rev * M i i.rev = 1 := by
    rcases hn with rfl | rfl
    · have hm : M 0 1 ≠ 0 := by simpa using hMr 0
      have hm' : M 1 0 = M 0 1 := hMsym 0 1
      refine ⟨![1, (M 0 1)⁻¹], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hm]
      · intro i
        fin_cases i <;> simp [hm'] <;> field_simp
    · have hm : M 0 2 ≠ 0 := by simpa using hMr 0
      have hm' : M 2 0 = M 0 2 := hMsym 0 2
      have hq : M 1 1 ≠ 0 := by simpa using hMr 1
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (M 1 1)⁻¹
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp [hq] at hz
      refine ⟨![1, z, (M 0 2)⁻¹], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hm, hz0]
      · intro i
        fin_cases i <;> simp [hm'] <;> field_simp
        rw [sq, ← hz, inv_mul_cancel₀ hq]
  refine ⟨V * Matrix.diagonal c, ?_, ?_, ?_⟩
  · exact hV.mul ((Matrix.isUnit_diagonal).2 (Pi.isUnit_iff.2 fun i => (hc0 i).isUnit))
  · ext i j
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    have e : Matrix.diagonal c * Vᵀ * Q * (V * Matrix.diagonal c) = Matrix.diagonal c * M * Matrix.diagonal c := by
      rw [hMdef]
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_diagonal, Matrix.diagonal_mul, Jmat]
    split_ifs with hj
    · subst hj
      linear_combination hc i
    · rw [hM0 i j hj]
      ring
  · rw [← Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    ring

private theorem ordProd_conj {H K : Type} [CommRing K] {n : ℕ} (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) (h : ordProd r ψ g = 0) :
    ordProd (fun s => (MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct P)) (r s)) ψ g = 0 := by
  set φ := MulSemiringAction.toRingHom _ (Matrix (Fin n) (Fin n) K) (ConjAct.toConjAct P)
  have hs : ∀ (c : K), φ (c • (1 : Matrix (Fin n) (Fin n) K)) = c • 1 := by
    intro c
    simp only [φ, MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct,
      mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]
  have : ordProd (fun s => φ (r s)) ψ g = φ (ordProd r ψ g) := by
    unfold ordProd
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp, map_sub, hs]
  rw [this, h, map_zero]

theorem UpperTheory.V.Fr.of_form :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [IsAlgClosed K] [Algebra C K], Function.Injective (algebraMap C K) → ∀ (r : F.G0 →* Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) K) (t : F.G0 → C) (χ : ∀ v, Fin n → F.Gv v →* Cˣ), IsUnit Q → Qᵀ = Q → (∀ g, (r g)ᵀ * Q * r (F.conj g) = Q) → IsTr O F n t → (∀ g, algebraMap C K (t g) = (r g).trace) → IsPsi O F n (fun v i g => (χ v i g : C)) → (∀ v g, ordProd (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g = 0) → ∃ (ρ : NRep F n K) (h : GL (Fin n) K), (∀ g, ρ.r g = h * r g * h⁻¹) ∧ (∀ v i g, (ρ.ψ v i g : K) = algebraMap C K (χ v i g)) ∧ Integral O C ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r Q t χ hQ hQs hform htr ht hpsi hord
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)
  have hiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)
  have hst : ∀ g : F.G0, Q * r (F.star g) = (r g)ᵀ * Q := by
    intro g
    have h1 := hform g⁻¹
    have h2 : (r g)ᵀ * (r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    calc Q * r (F.star g) = (r g)ᵀ * ((r g⁻¹)ᵀ * Q * r (F.conj g⁻¹)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]; rfl
      _ = (r g)ᵀ * Q := by rw [h1]
  have hS := UpperTheory.V.Fr.star hF
  have htrs : ∀ g : F.G0, (r (F.star g)).trace = (r g).trace := by
    intro g
    have : r (F.star g) = Q⁻¹ * ((r g)ᵀ * Q) := by
      rw [← hst g, ← Matrix.mul_assoc, hiQ, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hQi, Matrix.mul_one, Matrix.trace_transpose]
  set A := r F.g0 with hA
  set B := r (F.star F.g0) with hB
  set D := A - B with hDdef
  have hBt : Bᵀ * Q = Q * A := by
    have := hst (F.star F.g0)
    rw [hS.1] at this
    exact this.symm
  have hskew : Dᵀ * Q = -(Q * D) := by
    rw [hDdef, Matrix.transpose_sub, Matrix.sub_mul, hBt, Matrix.mul_sub, ← hst F.g0]
    abel
  have hDD : (D * D).trace = 2 * ((r (F.g0 * F.g0)).trace - (r (F.g0 * F.star F.g0)).trace) := by
    have e1 : (B * B).trace = (A * A).trace := by
      rw [hB, ← map_mul, ← hS.2.1, htrs, map_mul]
    have e2 : (B * A).trace = (A * B).trace := Matrix.trace_mul_comm _ _
    rw [map_mul, map_mul, ← hA, ← hB, hDdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, e1, e2]
    ring
  set a : (ResidueField O)ˣ := F.Ψ (F.g0 : F.Γ) with ha
  set z : ResidueField O := (a : ResidueField O) - ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) with hz
  have hab : (a : ResidueField O) * ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) = 1 := Units.mul_inv a
  have hz0 : z ≠ 0 := by
    intro h0
    apply hF.baseSubgroup_spec
    rw [← ha, sq]
    apply Units.val_injective
    rw [Units.val_mul, Units.val_one]
    have : (a : ResidueField O) = ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) := sub_eq_zero.1 h0
    nth_rewrite 2 [this]
    exact hab
  have hP1 : F.Ψ ((F.g0 * F.g0 : F.G0) : F.Γ) = a * a := by
    rw [Subgroup.coe_mul, map_mul]
  have hP2 : F.Ψ ((F.g0 * F.star F.g0 : F.G0) : F.Γ) = 1 := by
    rw [Subgroup.coe_mul, map_mul, hS.2.2.1, mul_inv_cancel]
  set X : C := t (F.g0 * F.g0) - t (F.g0 * F.star F.g0) with hX
  have hresX : res O C X = z ^ 2 := by
    have hb : (a : ResidueField O) ≠ 0 := a.ne_zero
    rw [hX, map_sub, htr.2, htr.2, hP1, hP2, hz, Units.val_inv_eq_inv_val]
    rcases hn with rfl | rfl
    · simp [Fin.sum_univ_two, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]
      field_simp
      ring
    · simp [Fin.sum_univ_three, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]
      field_simp
      ring
  have hk2 : (2 : ResidueField O) ≠ 0 := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    intro h0
    have h2 : (l : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)
    have hl : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact hl.one_lt.ne' h
    · exact hF.l_odd h
  have hC2 : IsUnit (2 : C) := by
    by_contra hc
    have hm : (2 : C) ∈ maximalIdeal C := (IsLocalRing.mem_maximalIdeal _).2 hc
    rw [← res_eq_zero_iff O, map_ofNat] at hm
    exact hk2 hm
  obtain ⟨ζ, hζr, hζX⟩ := co_sqrt hC2 X z hz0 hresX
  set ζK : K := algebraMap C K ζ with hζK
  have hK2 : (2 : K) ≠ 0 := by
    have := hC2.map (algebraMap C K)
    rw [map_ofNat] at this
    exact this.ne_zero
  have hζ0 : ζK ≠ 0 := by
    intro h0
    apply hz0
    rw [← hζr, (map_eq_zero_iff _ hinj).1 h0, map_zero]
  have htrK : (D * D).trace = 2 * ζK ^ 2 := by
    rw [hDD, ← ht, ← ht, ← map_sub, ← hX, ← hζX, hζK, map_pow]
  have hv := skew_eig hn hK2 Q D ζK hQ hskew htrK
  obtain ⟨P, hPu, hPQ, hDP⟩ := skew_norm hn hK2 Q D ζK hζ0 hQ hQs hskew hv
  obtain ⟨U, hU⟩ := hPu
  have hPi : (U : Matrix (Fin n) (Fin n) K) * ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = 1 := U.mul_inv
  have hiP : ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) * (U : Matrix (Fin n) (Fin n) K) = 1 := U.inv_mul
  subst hU
  set Pm : Matrix (Fin n) (Fin n) K := (U : Matrix (Fin n) (Fin n) K) with hPm
  set Pi : Matrix (Fin n) (Fin n) K := ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) with hPim
  have hconj : ∀ M : Matrix (Fin n) (Fin n) K,
      (MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹)) M = Pi * M * Pm := by
    intro M
    simp [MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, hPim, hPm]
  have e1 : Q * Pm = Piᵀ * Jmat K n := by
    rw [← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hPi, Matrix.transpose_one, Matrix.one_mul]
  have e2 : Pmᵀ * Q = Jmat K n * Pi := by
    rw [← hPQ, Matrix.mul_assoc (Pmᵀ * Q), hPi, Matrix.mul_one]
  let ρr : F.G0 →* Matrix (Fin n) (Fin n) K :=
    ((MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹) : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →* Matrix (Fin n) (Fin n) K).comp r
  have hρ : ∀ g, ρr g = Pi * r g * Pm := fun g => hconj (r g)
  have hpol : ∀ g, ρr (F.star g) = Jmat K n * (ρr g)ᵀ * Jmat K n := by
    intro g
    rw [hρ, hρ, Matrix.transpose_mul, Matrix.transpose_mul]
    calc Pi * r (F.star g) * Pm = (Jmat K n * Jmat K n) * Pi * r (F.star g) * Pm := by
          rw [Jmat_mul_Jmat, Matrix.one_mul]
      _ = Jmat K n * (Pmᵀ * Q) * r (F.star g) * Pm := by
          rw [e2]; simp only [Matrix.mul_assoc]
      _ = Jmat K n * Pmᵀ * ((r g)ᵀ * Q) * Pm := by
          rw [← hst]; simp only [Matrix.mul_assoc]
      _ = Jmat K n * Pmᵀ * (r g)ᵀ * (Q * Pm) := by
          simp only [Matrix.mul_assoc]
      _ = Jmat K n * (Pmᵀ * ((r g)ᵀ * Piᵀ)) * Jmat K n := by
          rw [e1]; simp only [Matrix.mul_assoc]
  have hdm : Pi * r F.g0 * Pm - Pi * r (F.star F.g0) * Pm = Matrix.diagonal fun i => (w n i : K) * ζK := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← hA, ← hB, ← hDdef, Matrix.mul_assoc, hDP, ← Matrix.mul_assoc, hiP, Matrix.one_mul]
  refine ⟨⟨ρr, fun v i => (Units.map (algebraMap C K : C →* K)).comp (χ v i), hpol, ?_, ?_⟩, U⁻¹, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hρ, hρ, hdm, Matrix.diagonal_apply_ne _ hij]
  · intro v g
    exact ordProd_conj U⁻¹ (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g (hord v g)
  · intro g
    rw [inv_inv]
    exact hρ g
  · intro v i g
    rfl
  · refine ⟨⟨t, htr, fun g => ?_⟩, ⟨fun v i g => (χ v i g : C), hpsi, fun v i g => rfl⟩, ⟨ζ, hζr, fun i => ?_⟩⟩
    · change algebraMap C K (t g) = (ρr g).trace
      rw [ht, hρ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
    · change (ρr F.g0 - ρr (F.star F.g0)) i i = _
      rw [hρ, hρ, hdm, Matrix.diagonal_apply_eq]
