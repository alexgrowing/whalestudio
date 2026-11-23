import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

section

variable {B : Type} [CommRing B]

private theorem triM_mul (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triM t x y z * triM s x' y' z' =
      triM (fun i => t i * s i) (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
        (z + x * (((t 1 / t 2 : Bˣ) : B) * y') + ((t 0 / t 2 : Bˣ) : B) * z') := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    first
    | ring1
    | linear_combination (-((t 0 : B) * x' * (s 1 : B))) * h1
    | linear_combination (-((t 0 : B) * z' * (s 2 : B)) - (s 2 : B) * x * (t 1 : B) * y') * h2
    | linear_combination (-((t 1 : B) * y' * (s 2 : B))) * h2

private theorem triM_inj {t s : Fin 3 → Bˣ} {x y z x' y' z' : B} (h : triM t x y z = triM s x' y' z') :
    t = s ∧ x = x' ∧ y = y' ∧ z = z' := by
  have e : ∀ i j, triM t x y z i j = triM s x' y' z' i j := fun i j => by rw [h]
  have a0 := e 0 0
  have a1 := e 1 1
  have a2 := e 2 2
  have b1 := e 0 1
  have b2 := e 1 2
  have b3 := e 0 2
  simp [triM] at a0 a1 a2 b1 b2 b3
  have ht : t = s := by
    funext i
    fin_cases i
    · exact Units.ext a0
    · exact Units.ext a1
    · exact Units.ext a2
  subst ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using congrArg (· * ((t 1)⁻¹ : Bˣ).val) b1
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b2
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b3

private theorem theta_triM {A : GL (Fin 3) B} {t : Fin 3 → Bˣ} {x y z : B}
    (h : (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z) :
    (theta A : Matrix (Fin 3) (Fin 3) B) = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  have key : triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) = 1 := by
    rw [theta_inv_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triM, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.rev] <;>
      first
      | linear_combination y * h2
      | linear_combination z * h2 - x * y * h1
      | linear_combination x * h1
  calc (theta A : Matrix (Fin 3) (Fin 3) B)
      = 1 * (theta A : Matrix (Fin 3) (Fin 3) B) := (one_mul _).symm
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) *
          (theta A : Matrix (Fin 3) (Fin 3) B) := by rw [key]
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem exists_triM (A : GL (Fin 3) B)
    (h : ∀ a b, wt a b < 0 → (A : Matrix (Fin 3) (Fin 3) B) a b = 0) :
    ∃ (t : Fin 3 → Bˣ) (x y z : B), (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z := by
  have z10 := h 1 0 (by decide)
  have z20 := h 2 0 (by decide)
  have z21 := h 2 1 (by decide)
  have hd : IsUnit (A : Matrix (Fin 3) (Fin 3) B).det := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_three, z10, z20, z21] at hd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero, IsUnit.mul_iff] at hd
  obtain ⟨⟨h0, h1⟩, h2⟩ := hd
  refine ⟨![h0.unit, h1.unit, h2.unit], (A : Matrix (Fin 3) (Fin 3) B) 0 1 * ↑h1.unit⁻¹,
    (A : Matrix (Fin 3) (Fin 3) B) 1 2 * ↑h2.unit⁻¹, (A : Matrix (Fin 3) (Fin 3) B) 0 2 * ↑h2.unit⁻¹, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, z10, z20, z21, mul_assoc]

end

theorem UpperTheory.exists_torus_coords_of_unipotent :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (h : B), 2 * h = 1 → ∀ u : G →* GG 3 B, HasMult η u → (∀ g a b, wt a b < 0 → (u g).mat a b = 0) → ∃ (T : Tor η B) (β : G → B × B) (γ : G → B), T.Coord h β γ u ∧ (∀ g g', β (g * g') = β g + T.M1 g (β g')) ∧ T.IsGam h β γ := by
  intro G B _ _ η h h2 u hm hu
  have ex : ∀ g, ∃ (t : Fin 3 → Bˣ) (x y z : B), (u g).mat = triM t x y z :=
    fun g => exists_triM (u g).left (hu g)
  choose t x y z hA using ex
  have step : ∀ g g', ∃ (t' : Fin 3 → Bˣ) (x' y' z' : B),
      (u (g * g')).mat = triM (t g) (x g) (y g) (z g) * triM t' x' y' z' ∧
      ((η g = 1 ∧ t' = t g' ∧ x' = x g' ∧ y' = y g' ∧ z' = z g') ∨
       (η g = -1 ∧ t' = (fun i => (t g' i.rev)⁻¹) ∧ x' = -y g' ∧ y' = -x g' ∧ z' = x g' * y g' - z g')) := by
    intro g g'
    have hmul : (u (g * g')).mat = (u g).mat * (((sgnAct 3 B) (u g).right) (u g').left : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul]
      show (((u g * u g').left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
      rw [SemidirectProduct.mul_left, Units.val_mul]
      rfl
    rw [hm g] at hmul
    rcases Int.units_eq_one_or (η g) with e | e
    · rw [e, sgnAct_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (hA g'), Or.inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [e, sgnAct_neg_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (theta_triM (hA g')), Or.inr ⟨e, rfl, rfl, rfl, rfl⟩⟩
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hab : ∀ g, ((t g 0 / t g 1 : Bˣ) : B) * ((t g 1 / t g 2 : Bˣ) : B) = ((t g 0 / t g 2 : Bˣ) : B) := by
    intro g
    rw [← Units.val_mul, div_mul_div_cancel]
  refine ⟨⟨t, ?_⟩, fun g => (x g, y g), fun g => z g - h * x g * y g, ⟨hm, fun g => ?_⟩, ?_, ?_⟩
  · intro g g' i
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨ht, -, -, -⟩ := triM_inj he
    rcases hc with ⟨e, rfl, -, -, -⟩ | ⟨e, rfl, -, -, -⟩
    · rw [ht]
      simp [e]
    · rw [ht]
      simp [e, hne]
  · rw [hA g]
    congr 1
    ring
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, -⟩ := triM_inj he
    rcases hc with ⟨e, -, rfl, rfl, -⟩ | ⟨e, -, rfl, rfl, -⟩
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hx, hy]
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hne, hx, hy]
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, hz⟩ := triM_inj he
    have hg := hab g
    simp only [Tor.χ2_apply, Tor.adjointSuperdiagRep_apply, omg]
    rcases hc with ⟨e, -, rfl, rfl, rfl⟩ | ⟨e, -, rfl, rfl, rfl⟩
    · simp only [e, if_true]
      rw [hx, hy, hz]
      push_cast
      linear_combination (-(x g * ((t g 1 / t g 2 : Bˣ) : B) * y g')) * h2 - (h * x g' * y g') * hg
    · simp only [e, hne, if_false]
      rw [hx, hy, hz]
      push_cast
      linear_combination (((t g 1 / t g 2 : Bˣ) : B) * x g * x g' - ((t g 0 / t g 2 : Bˣ) : B) * x g' * y g') * h2 - (h * x g' * y g') * hg
