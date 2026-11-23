import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rbar_J {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * Xᵀ * Jmat K n) i j = X j.rev i.rev := by
  have h : ∀ x : Fin n, j = x.rev ↔ x = j.rev := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, Jmat, h]

private theorem rbar_w {n : ℕ} (i : Fin n) : w n i.rev = - w n i := by
  have hi := i.2
  unfold w
  rw [Fin.val_rev]
  split_ifs with h <;> omega

private theorem rbar_prod {K : Type} [CommRing K] {n : ℕ} (L : List (Fin n → K)) :
    (L.map fun d => Matrix.diagonal d).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp [← Matrix.diagonal_one]
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal, List.prod_cons]; rfl

private theorem rbar_ord {H K : Type} [CommRing K] {n : ℕ} (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => Matrix.diagonal fun j => ψ j s) ψ g = 0 := by
  unfold ordProd
  have e : (List.ofFn fun i => (Matrix.diagonal fun j => ψ j (g i)) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) K)) =
      (List.ofFn fun i => fun j => ψ j (g i) - ψ i (g i)).map fun d => Matrix.diagonal d := by
    rw [List.map_ofFn]
    congr 1
    funext i
    ext a b
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  rw [e, rbar_prod, List.prod_ofFn, ← Matrix.diagonal_zero]
  congr 1
  funext j
  rw [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)

theorem UpperTheory.V.Fr.rbar :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → ∃ ρ : NRep F n k, ρ.IsBar (RingHom.id k) ∧ ρ.IsDiag := by
  intro l _ k _ _ F C₀ n _
  have hs : ∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹ := fun g => by
    have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
  refine ⟨{ r := { toFun := fun g => Matrix.diagonal fun i => ((F.Ψ g ^ w n i : kˣ) : k)
                   map_one' := by simp
                   map_mul' := fun g h => by simp [Matrix.diagonal_mul_diagonal, mul_zpow] }
            ψ := fun v i => (zpowGroupHom (w n i)).comp (F.Ψ.comp (F.loc v))
            pol := fun g => ?_
            diag := fun i j h => ?_
            ord := fun v g => ?_ }, ⟨fun g i => ?_, fun v i g => rfl⟩, fun g i j h => ?_⟩
  · ext i j
    rw [rbar_J]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, hs]
    by_cases h : i = j
    · subst h
      simp [rbar_w]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      exact fun e => h (Fin.rev_injective e).symm
  · simp [Matrix.diagonal_apply_ne _ h]
  · exact rbar_ord (fun i s => ((F.Ψ (F.loc v s) ^ w n i : kˣ) : k)) g
  · simp
  · exact Matrix.diagonal_apply_ne _ h
