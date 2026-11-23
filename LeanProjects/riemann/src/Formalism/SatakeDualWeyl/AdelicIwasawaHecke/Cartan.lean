import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

open Matrix

namespace Formalism.UG.P

section Smith

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n]

theorem cartan_mulVec_injective (G : Matrix n n R) (hG : G.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin G) := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  by_contra hne
  exact hG (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hne, hv⟩)

theorem cartan_smith (G : Matrix n n R) (hG : G.det ≠ 0) :
    ∃ P C : Matrix n n R, IsUnit P.det ∧ IsUnit C.det ∧ ∃ a : n → R, (∀ i, a i ≠ 0) ∧
      G = P * Matrix.diagonal a * C := by
  have inj := cartan_mulVec_injective G hG
  let N := LinearMap.range (Matrix.mulVecLin G)
  let e0 : (n → R) ≃ₗ[R] N := LinearEquiv.ofInjective _ inj
  have hrank : Module.finrank R N = Module.finrank R (n → R) := e0.finrank_eq.symm
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun R n) hrank
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    apply ab'.ne_zero i
    apply Subtype.coe_injective
    simp [hab i, hi]
  let e : (n → R) ≃ₗ[R] (n → R) :=
    e0.trans (ab'.repr.trans (Finsupp.linearEquivFunOnFinite R R n))
  let P := (Pi.basisFun R n).toMatrix b'
  let C := LinearMap.toMatrix' (e : (n → R) →ₗ[R] (n → R))
  let C' := LinearMap.toMatrix' (e.symm : (n → R) →ₗ[R] (n → R))
  have hCC : C * C' = 1 := by
    simp only [C, C', ← LinearMap.toMatrix'_comp]
    have : (e : (n → R) →ₗ[R] (n → R)) ∘ₗ (e.symm : (n → R) →ₗ[R] (n → R)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hP : IsUnit P.det := by
    have := (Pi.basisFun R n).invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨P, C, hP, Matrix.isUnit_det_of_right_inverse hCC, a, ha, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hC : C *ᵥ x = e x := LinearMap.toMatrix'_mulVec _ x
  rw [hC]
  have hx : G *ᵥ x = ((e0 x : N) : n → R) := by
    show G *ᵥ x = ((LinearEquiv.ofInjective _ inj x : N) : n → R)
    rw [LinearEquiv.ofInjective_apply]; rfl
  rw [hx]
  conv_lhs => rw [← ab'.sum_repr (e0 x)]
  funext k
  simp only [Submodule.coe_sum, Submodule.coe_smul, hab, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [P, e, Module.Basis.toMatrix_apply, Finsupp.linearEquivFunOnFinite_apply]
  ring

end Smith

section Generic

variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]

theorem cartan_entries_of_mem (U : GL n L) (hU : U ∈ GLint n O) (i j : n) :
    (U : Matrix n n L) i j ∈ O := by
  obtain ⟨V, rfl⟩ := hU
  exact ((V : Matrix n n O) i j).2

theorem cartan_mem_of_entries (U : GL n L) (h1 : ∀ i j, (U : Matrix n n L) i j ∈ O)
    (h2 : ∀ i j, ((U⁻¹ : GL n L) : Matrix n n L) i j ∈ O) : U ∈ GLint n O := by
  have key : ∀ (A : Matrix n n L) (hA : ∀ i j, A i j ∈ O),
      (Matrix.of fun i j => (⟨A i j, hA i j⟩ : O)).map O.subtype = A := fun A hA => by
    ext
    rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨(U : Matrix n n L) i j, h1 i j⟩,
    Matrix.of fun i j => ⟨((U⁻¹ : GL n L) : Matrix n n L) i j, h2 i j⟩, ?_, ?_⟩, ?_⟩
  · apply hinj
    dsimp only
    rw [Matrix.map_mul, key, key, Matrix.map_one _ (map_zero _) (map_one _)]
    exact U.mul_inv
  · apply hinj
    dsimp only
    rw [Matrix.map_mul, key, key, Matrix.map_one _ (map_zero _) (map_one _)]
    exact U.inv_mul
  · exact Units.ext (key _ h1)

theorem cartan_exists_glint (A B : Matrix n n L) (hAB : A * B = 1) (hA : ∀ i j, A i j ∈ O)
    (hB : ∀ i j, B i j ∈ O) : ∃ U ∈ GLint n O, (U : Matrix n n L) = A := by
  refine ⟨⟨A, B, hAB, mul_eq_one_comm.mp hAB⟩, ?_, rfl⟩
  exact cartan_mem_of_entries O _ hA hB

theorem cartan_det_mem (M : Matrix n n L) (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  rw [Matrix.det_apply]
  refine sum_mem (fun σ _ => ?_)
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem cartan_val_det (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (U : GL n L)
    (hU : U ∈ GLint n O) : val (U : Matrix n n L).det = 1 := by
  have h1 := cartan_entries_of_mem O U hU
  have h2 := cartan_entries_of_mem O U⁻¹ (inv_mem hU)
  have ha : val (U : Matrix n n L).det ≤ 1 := (hO _).mp (cartan_det_mem O _ h1)
  have hb : val ((U⁻¹ : GL n L) : Matrix n n L).det ≤ 1 := (hO _).mp (cartan_det_mem O _ h2)
  have hprod : val (U : Matrix n n L).det * val ((U⁻¹ : GL n L) : Matrix n n L).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      map_one]
  refine le_antisymm ha ?_
  calc (1 : Γ) = _ := hprod.symm
    _ ≤ _ := mul_le_of_le_one_right' hb

end Generic

section Unique

variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem cartan_pigeon {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ∃ j, j ≤ i ∧ i ≤ σ j := by
  by_contra hne
  push_neg at hne
  have hmaps : Set.MapsTo σ (Finset.Iic i : Set (Fin m)) (Finset.Iio i : Set (Fin m)) := by
    intro j hj
    simp only [Finset.coe_Iic, Finset.coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
    exact hne j hj
  have hc := Finset.card_le_card_of_injOn σ hmaps σ.injective.injOn
  simp at hc

theorem cartan_core (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hϖ : val ϖ < 1) {m : ℕ} (a b : Fin m → ℤ) (ha : Antitone a)
    (hb : Antitone b) (k : GL (Fin m) L) (hk : k ∈ GLint (Fin m) O)
    (k' : Matrix (Fin m) (Fin m) L) (hk' : ∀ i j, k' i j ∈ O)
    (h : Matrix.diagonal (fun i => ϖ ^ a i) * (k : Matrix (Fin m) (Fin m) L) =
      k' * Matrix.diagonal (fun i => ϖ ^ b i)) (i : Fin m) (hi : a i < b i) : False := by
  have hvϖ : val ϖ ≠ 0 := (Valuation.ne_zero_iff val).mpr hϖ0
  have hent : ∀ p q, ϖ ^ a p * (k : Matrix (Fin m) (Fin m) L) p q = k' p q * ϖ ^ b q := by
    intro p q
    have e := congrFun (congrFun h p) q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    exact e
  have hsmall : ∀ p q, i ≤ p → q ≤ i → val ((k : Matrix (Fin m) (Fin m) L) p q) < 1 := by
    intro p q hp hq
    have hkpq : (k : Matrix (Fin m) (Fin m) L) p q = k' p q * ϖ ^ (b q - a p) := by
      have h0 := zpow_ne_zero (a p) hϖ0
      rw [zpow_sub₀ hϖ0, ← mul_div_assoc, ← hent p q]
      field_simp
    have hap := ha hp
    have hbq := hb hq
    obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ b q - a p - 1 by omega)
    have hN' : b q - a p = (N : ℤ) + 1 := by omega
    have h1 : val (k' p q) ≤ 1 := (hO _).mp (hk' p q)
    have h2 : val ϖ ^ N ≤ 1 := pow_le_one' hϖ.le N
    rw [hkpq, map_mul, map_zpow₀, hN', zpow_add₀ hvϖ, zpow_natCast, zpow_one]
    calc val (k' p q) * (val ϖ ^ N * val ϖ) ≤ 1 * (1 * val ϖ) :=
          mul_le_mul' h1 (mul_le_mul' h2 le_rfl)
      _ = val ϖ := by rw [one_mul, one_mul]
      _ < 1 := hϖ
  have hle : ∀ p q, val ((k : Matrix (Fin m) (Fin m) L) p q) ≤ 1 :=
    fun p q => (hO _).mp (cartan_entries_of_mem O k hk p q)
  have hdet : val (k : Matrix (Fin m) (Fin m) L).det < 1 := by
    rw [Matrix.det_apply]
    refine Valuation.map_sum_lt val one_ne_zero (fun σ _ => ?_)
    obtain ⟨j, hj, hσj⟩ := cartan_pigeon σ i
    have hprod : val (∏ x, (k : Matrix (Fin m) (Fin m) L) (σ x) x) < 1 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), map_mul, map_prod]
      calc val ((k : Matrix (Fin m) (Fin m) L) (σ j) j) *
            ∏ x ∈ Finset.univ.erase j, val ((k : Matrix (Fin m) (Fin m) L) (σ x) x)
          ≤ val ((k : Matrix (Fin m) (Fin m) L) (σ j) j) * 1 :=
            mul_le_mul' le_rfl (Finset.prod_le_one' (fun x _ => hle _ _))
        _ < 1 := by rw [mul_one]; exact hsmall _ _ hσj hj
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
    · rw [one_smul]
      exact hprod
    · rw [Units.neg_smul, one_smul, Valuation.map_neg]
      exact hprod
  exact absurd (cartan_val_det O val hO k hk) (ne_of_lt hdet)

theorem cartan_unique_gen (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hϖ : val ϖ < 1) {m : ℕ} (a a' : Fin m → ℤ) (ha : Antitone a)
    (ha' : Antitone a') (k₁ : GL (Fin m) L) (hk₁ : k₁ ∈ GLint (Fin m) O)
    (k₂ : GL (Fin m) L) (hk₂ : k₂ ∈ GLint (Fin m) O)
    (h : (k₁ : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) *
      (k₂ : Matrix (Fin m) (Fin m) L) = Matrix.diagonal (fun i => ϖ ^ a' i)) : a = a' := by
  have hk₁i : k₁⁻¹ ∈ GLint (Fin m) O := inv_mem hk₁
  have hk₂i : k₂⁻¹ ∈ GLint (Fin m) O := inv_mem hk₂
  have e1 : Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin m) (Fin m) L) =
      ((k₁⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a' i) := by
    rw [← h, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have e2 : Matrix.diagonal (fun i => ϖ ^ a' i) * ((k₂⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) =
      (k₁ : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) := by
    rw [← h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  funext i
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    exact cartan_core O val hO ϖ hϖ0 hϖ a' a ha' ha k₂⁻¹ hk₂i _
      (cartan_entries_of_mem O k₁ hk₁) e2 i hlt
  · by_contra hlt
    push_neg at hlt
    exact cartan_core O val hO ϖ hϖ0 hϖ a a' ha ha' k₂ hk₂ _
      (cartan_entries_of_mem O k₁⁻¹ hk₁i) e1 i hlt

end Unique

section Decomp

variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem cartan_perm_glint {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    ∃ U ∈ GLint (Fin m) O, (U : Matrix (Fin m) (Fin m) L) = τ.toPEquiv.toMatrix := by
  obtain ⟨U, hU, hUA⟩ := cartan_exists_glint O τ.toPEquiv.toMatrix τ.symm.toPEquiv.toMatrix
    (by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl])
    (by intro i j; rw [PEquiv.toMatrix_apply]; split_ifs; exacts [O.one_mem, O.zero_mem])
    (by intro i j; rw [PEquiv.toMatrix_apply]; split_ifs; exacts [O.one_mem, O.zero_mem])
  exact ⟨U, hU, hUA⟩

theorem cartan_diag_perm {m : ℕ} (d : Fin m → L) (σ : Equiv.Perm (Fin m)) :
    Matrix.diagonal d = σ.symm.toPEquiv.toMatrix * Matrix.diagonal (d ∘ σ) * σ.toPEquiv.toMatrix := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, h]

theorem cartan_sort (ϖ : L) {m : ℕ} (a : Fin m → ℤ) :
    ∃ a' : Fin m → ℤ, Antitone a' ∧ ∃ S₁ ∈ GLint (Fin m) O, ∃ S₂ ∈ GLint (Fin m) O,
      Matrix.diagonal (fun i => ϖ ^ a i) = (S₁ : Matrix (Fin m) (Fin m) L) *
        Matrix.diagonal (fun i => ϖ ^ a' i) * (S₂ : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin m), Monotone ((fun i => -a i) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  obtain ⟨S₁, h₁, e₁⟩ := cartan_perm_glint (L := L) O σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := cartan_perm_glint (L := L) O σ
  refine ⟨a ∘ σ, fun i j hij => ?_, S₁, h₁, S₂, h₂, ?_⟩
  · have := hσ hij
    simp only [Function.comp_apply] at this ⊢
    omega
  · rw [e₁, e₂]
    exact cartan_diag_perm (fun i => ϖ ^ a i) σ

theorem cartan_diag_units (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hU : ∀ x : L, x ≠ 0 → ∃ k : ℤ, val x = val ϖ ^ k) {m : ℕ} (d : Fin m → L)
    (hd : ∀ i, d i ≠ 0) :
    ∃ a : Fin m → ℤ, ∃ U ∈ GLint (Fin m) O,
      Matrix.diagonal d = (U : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) := by
  choose a ha using fun i => hU (d i) (hd i)
  have hvϖ : val ϖ ≠ 0 := (Valuation.ne_zero_iff val).mpr hϖ0
  refine ⟨a, ?_⟩
  have hAB : (Matrix.diagonal fun i => d i * ϖ ^ (-a i)) * (Matrix.diagonal fun i => (d i)⁻¹ * ϖ ^ a i) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hd i
    have h2 := zpow_ne_zero (a i) hϖ0
    rw [_root_.zpow_neg]
    field_simp
  have hA : ∀ i j, (Matrix.diagonal fun i => d i * ϖ ^ (-a i)) i j ∈ O := by
    intro i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (hO _).mpr (le_of_eq (by
        rw [map_mul, map_zpow₀, ha i, ← zpow_add₀ hvϖ, add_neg_cancel, zpow_zero]))
    · exact O.zero_mem
  have hB : ∀ i j, (Matrix.diagonal fun i => (d i)⁻¹ * ϖ ^ a i) i j ∈ O := by
    intro i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (hO _).mpr (le_of_eq (by
        rw [map_mul, map_inv₀, map_zpow₀, ha i, inv_mul_cancel₀ (zpow_ne_zero _ hvϖ)]))
    · exact O.zero_mem
  obtain ⟨U, hUm, hUA⟩ := cartan_exists_glint O _ _ hAB hA hB
  refine ⟨U, hUm, ?_⟩
  rw [hUA, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, mul_one]

theorem cartan_decomp_gen [IsPrincipalIdealRing O] (val : Valuation L Γ)
    (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L) (hϖ0 : ϖ ≠ 0)
    (hU : ∀ x : L, x ≠ 0 → ∃ k : ℤ, val x = val ϖ ^ k) {m : ℕ} (g : GL (Fin m) L) (c : O)
    (hc : c ≠ 0) (hg : (c : L) • (g : Matrix (Fin m) (Fin m) L) ∈
      (RingHom.mapMatrix (m := Fin m) O.subtype).range) :
    ∃ a : Fin m → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin m) O, ∃ k₂ ∈ GLint (Fin m) O,
      (g : Matrix (Fin m) (Fin m) L) = (k₁ : Matrix (Fin m) (Fin m) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨G, hG⟩ := hg
  have hc' : (c : L) ≠ 0 := fun h => hc (Subtype.ext h)
  have hg0 : (g : Matrix (Fin m) (Fin m) L).det ≠ 0 := by
    have : (g : Matrix (Fin m) (Fin m) L).det * ((g⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this
  have hdet : G.det ≠ 0 := by
    intro h0
    have : O.subtype G.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, hG, Matrix.det_smul] at this
    exact mul_ne_zero (pow_ne_zero _ hc') hg0 this
  obtain ⟨P, C, hP, hC, d, hd, hPdC⟩ := cartan_smith G hdet
  let PL := bc (n := Fin m) O.subtype (Matrix.nonsingInvUnit P hP)
  let CL := bc (n := Fin m) O.subtype (Matrix.nonsingInvUnit C hC)
  have hPL : (PL : Matrix (Fin m) (Fin m) L) = RingHom.mapMatrix O.subtype P := rfl
  have hCL : (CL : Matrix (Fin m) (Fin m) L) = RingHom.mapMatrix O.subtype C := rfl
  let d' : Fin m → L := fun i => (c : L)⁻¹ * (d i : L)
  have hd' : ∀ i, d' i ≠ 0 := fun i =>
    mul_ne_zero (inv_ne_zero hc') (fun h => hd i (Subtype.ext h))
  have hgd : (g : Matrix (Fin m) (Fin m) L) = (PL : Matrix (Fin m) (Fin m) L) *
      Matrix.diagonal d' * (CL : Matrix (Fin m) (Fin m) L) := by
    have hX : (g : Matrix (Fin m) (Fin m) L) = (c : L)⁻¹ • ((c : L) • (g : Matrix (Fin m) (Fin m) L)) := by
      rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
    have hD : Matrix.diagonal d' = (c : L)⁻¹ • RingHom.mapMatrix O.subtype (Matrix.diagonal d) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.smul_apply,
        smul_eq_mul, d']
      split_ifs <;> simp
    rw [hX, ← hG, hPdC, map_mul, map_mul, hPL, hCL, hD, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨a, U, hUm, hUe⟩ := cartan_diag_units O val hO ϖ hϖ0 hU d' hd'
  obtain ⟨a', ha', S₁, h₁, S₂, h₂, hS⟩ := cartan_sort O ϖ a
  refine ⟨a', ha', PL * U * S₁, mul_mem (mul_mem ⟨_, rfl⟩ hUm) h₁, S₂ * CL,
    mul_mem h₂ ⟨_, rfl⟩, ?_⟩
  rw [hgd, hUe, hS]
  simp only [Units.val_mul, Matrix.mul_assoc]

end Decomp

section Adic

open IsDedekindDomain NumberField

theorem cartan_mem_Ov (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  first
  | exact Iff.rfl
  | exact HeightOneSpectrum.mem_adicCompletionIntegers F v

theorem cartan_unif_ne_zero (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  unfold IsUnifV at h
  intro h0
  rw [h0, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

theorem cartan_unif_lt_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  first
  | exact WithZero.coe_lt_coe.mpr (by decide)
  | exact WithZero.coe_lt_one.mpr (by decide)
  | decide

theorem cartan_val_pow (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ∃ k : ℤ, Valued.v x = Valued.v ϖ ^ k := by
  unfold IsUnifV at h
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hx0
  refine ⟨-(Multiplicative.toAdd g), ?_⟩
  rw [h, ← hg, ← WithZero.coe_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem cartan_decomposition_holds : Formalism.UG.CartanDecomp := by
  intro F _ _ v n ϖ _ hU g
  obtain ⟨c, hc0, hg, -⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have : IsPrincipalIdealRing (Ov F v) :=
    inferInstanceAs (IsPrincipalIdealRing (v.adicCompletionIntegers F))
  exact cartan_decomp_gen (Ov F v) (Valued.v) (cartan_mem_Ov F v) ϖ (cartan_unif_ne_zero F v ϖ hU)
    (cartan_val_pow F v ϖ hU) g c hc0 hg

theorem cartan_decomposition_unique_holds : Formalism.UG.CartanUnique := by
  unfold Formalism.UG.CartanUnique
  intro F _ _ v n ϖ _ hϖ a a' ha ha' k₁ hk₁ k₂ hk₂ h
  unfold diagPow at h
  exact cartan_unique_gen (Ov F v) Valued.v (cartan_mem_Ov F v) ϖ (cartan_unif_ne_zero F v ϖ hϖ)
    (cartan_unif_lt_one F v ϖ hϖ) a a' ha ha' k₁ hk₁ k₂ hk₂ h

end Adic

end Formalism.UG.P
