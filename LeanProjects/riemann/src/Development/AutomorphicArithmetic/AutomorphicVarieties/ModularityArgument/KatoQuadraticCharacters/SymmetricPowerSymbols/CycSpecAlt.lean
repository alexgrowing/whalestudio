import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

private theorem ex_root (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {M : ℕ} (hM : 0 < M) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (M : Ω) := ⟨by
    rw [← map_natCast (algebraMap ℚ Ω)]
    exact (map_ne_zero _).2 (by exact_mod_cast hM.ne')⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω M

private theorem pow_emod_order_eq_pow_of_pow_eq_one {F : Type} [Field F] {z : F} {m : ℕ} (h : z ^ m = 1) (k : ℕ) :
    z ^ (k % m) = z ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

private theorem cyc_spec {M : ℕ} (hM : 0 < M) (s : Ω ≃ₐ[ℚ] Ω) : ∀ z : Ω, z ^ M = 1 → s z = z ^ (cyc M s).val := by
  obtain ⟨ζ, h⟩ := ex_root Ω hM
  haveI : NeZero M := ⟨hM.ne'⟩
  have hsm : (s ζ) ^ M = 1 := by rw [← map_pow, h.pow_eq_one, map_one]
  obtain ⟨k, -, hk⟩ := h.eq_pow_of_pow_eq_one hsm
  have hex : ∃ y : ZMod M, ∀ z : Ω, z ^ M = 1 → s z = z ^ y.val := by
    refine ⟨(k : ZMod M), fun z hz => ?_⟩
    obtain ⟨i, -, hi⟩ := h.eq_pow_of_pow_eq_one hz
    have hiM : (ζ ^ i) ^ M = 1 := by rw [hi]; exact hz
    rw [← hi, map_pow, ← hk, ZMod.val_natCast, pow_emod_order_eq_pow_of_pow_eq_one hiM, ← pow_mul, ← pow_mul, mul_comm]
  unfold cyc
  exact Classical.epsilon_spec hex

private theorem cyc_uniq {M : ℕ} (hM : 0 < M) (s : Ω ≃ₐ[ℚ] Ω) (n : ℕ) (h : ∀ z : Ω, z ^ M = 1 → s z = z ^ n) :
    cyc M s = n := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := ex_root Ω hM
  have e : ζ ^ (cyc M s).val = ζ ^ ((n : ZMod M)).val := by
    rw [← cyc_spec hM s ζ hζ.pow_eq_one, h ζ hζ.pow_eq_one, ZMod.val_natCast,
      pow_emod_order_eq_pow_of_pow_eq_one hζ.pow_eq_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e)

private theorem cyc_mul {M : ℕ} (hM : 0 < M) (s t : Ω ≃ₐ[ℚ] Ω) : cyc M (s * t) = cyc M s * cyc M t := by
  rw [cyc_uniq hM (s * t) ((cyc M s).val * (cyc M t).val) ?_]
  · haveI : NeZero M := ⟨hM.ne'⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · intro z hz
    rw [AlgEquiv.mul_apply, cyc_spec hM t z hz, map_pow, cyc_spec hM s z hz, ← pow_mul]

private theorem cyc_one {M : ℕ} (hM : 0 < M) : cyc M (1 : Ω ≃ₐ[ℚ] Ω) = 1 := by
  rw [cyc_uniq hM 1 1 (fun z _ => by rw [AlgEquiv.one_apply, pow_one]), Nat.cast_one]

private theorem cyc_cast {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (s : Ω ≃ₐ[ℚ] Ω) :
    ZMod.castHom (dvd_mul_left M k) (ZMod M) (cyc (k * M) s) = cyc M s := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (k * M) := ⟨(Nat.mul_pos hk hM).ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  symm
  apply cyc_uniq hM s
  intro z hz
  apply cyc_spec (Nat.mul_pos hk hM) s z
  rw [mul_comm, pow_mul, hz, one_pow]

private theorem gr_mul {M : ℕ} (hM : 0 < M) (s t : Ω ≃ₐ[ℚ] Ω) (x : Row M) : gr M (s * t) x = gr M s (gr M t x) := by
  simp [gr, cyc_mul hM, mul_assoc]

private theorem gr_one {M : ℕ} (hM : 0 < M) (x : Row M) : gr M (1 : Ω ≃ₐ[ℚ] Ω) x = x := by
  ext i; fin_cases i <;> simp [gr, cyc_one hM]

private theorem gr_ne {M : ℕ} (hM : 0 < M) (s : Ω ≃ₐ[ℚ] Ω) (x : Row M) (h : (2 : ZMod M) • x ≠ 0) :
    (2 : ZMod M) • gr M s x ≠ 0 := by
  have hinv : cyc M s⁻¹ * cyc M s = 1 := by rw [← cyc_mul hM, inv_mul_cancel, cyc_one hM]
  intro h0
  apply h
  funext i
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  simp only [gr, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at e0 e1
  fin_cases i
  · simpa using e0
  · show (2 : ZMod M) * x 1 = 0
    linear_combination (cyc M s⁻¹) * e1 - (2 * x 1) * hinv

end

private theorem rt_ne {M : ℕ} (γ : SL(2, ℤ)) (x : Row M) (h : (2 : ZMod M) • x ≠ 0) :
    (2 : ZMod M) • rt x γ ≠ 0 := by
  intro h0
  apply h
  set A : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) with hA
  have hdet : A.det = 1 := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
  have h1 : ((2 : ZMod M) • x) ᵥ* A = 0 := by
    rw [Matrix.smul_vecMul]
    exact h0
  calc (2 : ZMod M) • x = ((2 : ZMod M) • x) ᵥ* (A * A.adjugate) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]

private theorem up_val {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (x : Row M) (i : Fin 2) : (up k M x i).val = k * (x i).val := by
  haveI : NeZero M := ⟨hM.ne'⟩
  show ((k * (x i).val : ℕ) : ZMod (k * M)).val = k * (x i).val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ((Nat.mul_lt_mul_left hk).2 (ZMod.val_lt _))]

private theorem up_mul {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (c : ZMod (k * M)) (a : ZMod M) :
    c * ((k * a.val : ℕ) : ZMod (k * M)) = ((k * (ZMod.castHom (dvd_mul_left M k) (ZMod M) c * a).val : ℕ) : ZMod (k * M)) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (k * M) := ⟨(Nat.mul_pos hk hM).ne'⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ZMod (k * M)) = c := ⟨c.val, ZMod.natCast_zmod_val c⟩
  rw [map_natCast]
  have e : ((n : ZMod M) * a).val = (n * a.val) % M := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  have h1 : k * (n * a.val % M) ≡ k * (n * a.val) [MOD k * M] := (Nat.mod_modEq _ _).mul_left' k
  refine Nat.ModEq.trans ?_ h1.symm
  rw [show n * (k * a.val) = k * (n * a.val) by ring]

private theorem up_ne {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (x : Row M) (h : (2 : ZMod M) • x ≠ 0) :
    (2 : ZMod (k * M)) • up k M x ≠ 0 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  intro h0
  apply h
  funext i
  have e := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, up] at e ⊢
  have e' : (((2 * (k * (x i).val)) : ℕ) : ZMod (k * M)) = 0 := by exact_mod_cast e
  rw [ZMod.natCast_eq_zero_iff] at e'
  have hd : M ∣ 2 * (x i).val := by
    apply Nat.dvd_of_mul_dvd_mul_left hk
    rw [show k * (2 * (x i).val) = 2 * (k * (x i).val) by ring]
    exact e'
  have h2 : ((2 * (x i).val : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at h2
  simpa [ZMod.natCast_zmod_val] using h2

private theorem dn_ne {k M : ℕ} (x : Row (k * M)) (h : (2 : ZMod M) • dn k M x ≠ 0) :
    (2 : ZMod (k * M)) • x ≠ 0 := by
  intro h0
  apply h
  funext i
  have e := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
  show (2 : ZMod M) * ZMod.castHom (dvd_mul_left M k) (ZMod M) (x i) = 0
  rw [← map_ofNat (ZMod.castHom (dvd_mul_left M k) (ZMod M)) 2, ← map_mul, e, map_zero]

theorem UpperTheory.V.Z.Kato.Sym.rowB :
    UpperTheory.V.Z.Kato.Sym.RowB := by
  intro Ω _ _ _ M hM
  haveI : NeZero M := ⟨hM.ne'⟩
  have hne : ∀ {N : ℕ} (x : Row N), (2 : ZMod N) • x ≠ 0 → x ≠ 0 := by
    intro N x hx h0
    apply hx
    rw [h0, smul_zero]
  refine ⟨fun s t x => ⟨gr_mul hM s t x, gr_one hM x⟩, ?_, ?_, ?_⟩
  · intro x y hxy
    exact ⟨hne x hxy.1, hne y hxy.2, fun s => ⟨gr_ne hM s x hxy.1, gr_ne hM s y hxy.2⟩,
      fun γ => ⟨rt_ne γ x hxy.1, rt_ne γ y hxy.2⟩⟩
  · intro γ x hγ
    have e := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)))
      ((CongruenceSubgroup.Gamma_mem').1 hγ)
    simp only [Matrix.SpecialLinearGroup.coe_one] at e
    show x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = x
    rw [show (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = 1 from e,
      Matrix.vecMul_one]
  · intro k hk
    haveI : NeZero (k * M) := ⟨(Nat.mul_pos hk hM).ne'⟩
    refine ⟨?_, fun x y hxy => ⟨up_ne hk hM x hxy.1, up_ne hk hM y hxy.2⟩, ?_,
      fun x' y' hxy => ⟨dn_ne x' hxy.1, dn_ne y' hxy.2⟩, ?_, ?_, ?_⟩
    · intro x
      funext i
      simp only [toQ, up_val hk hM]
      push_cast
      rw [mul_div_mul_left _ _ (by exact_mod_cast hk.ne' : (k : ℚ) ≠ 0)]
    · intro s x
      funext i
      fin_cases i
      · rfl
      · show cyc (k * M) s * ((k * (x 1).val : ℕ) : ZMod (k * M)) =
          ((k * (cyc M s * x 1).val : ℕ) : ZMod (k * M))
        rw [up_mul hk hM, cyc_cast hk hM]
    · intro s x'
      funext i
      fin_cases i
      · rfl
      · show ZMod.castHom (dvd_mul_left M k) (ZMod M) (cyc (k * M) s * x' 1) =
          cyc M s * ZMod.castHom (dvd_mul_left M k) (ZMod M) (x' 1)
        rw [map_mul, cyc_cast hk hM]
    · intro γ x'
      funext i
      simp [dn, rt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · intro y
      refine ⟨fun i => ((y i).val : ZMod (k * M)), ?_⟩
      funext i
      simp [dn, ZMod.natCast_zmod_val]
