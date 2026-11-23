import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SignLemma
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.SkolemNoether

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zero_of_trace {G K : Type} [Monoid G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) (X : Matrix (Fin n) (Fin n) K) (hX : ∀ g, (ρ g * X).trace = 0) :
    X = 0 := by
  have hall : ∀ M : Matrix (Fin n) (Fin n) K, (M * X).trace = 0 := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := by rw [h]; trivial
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hX t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  simpa [Matrix.trace_single_mul] using hall (Matrix.single j i 1)

private theorem span_of_trace {G C K K' : Type} [Monoid G] [CommRing C] [Field K] [Field K'] {n : ℕ}
    (f : C →+* K) (hf : Function.Injective f) (φ : C →+* K') (t : G → C)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (ρ' : G →* Matrix (Fin n) (Fin n) K')
    (h : ∀ g, f (t g) = (ρ g).trace) (h' : ∀ g, φ (t g) = (ρ' g).trace)
    (hs : Submodule.span K' (Set.range ρ') = ⊤) : Submodule.span K (Set.range ρ) = ⊤ := by
  obtain ⟨g, hg⟩ := (UpperTheory.V.AlgebraTools.Det.gramIff ρ').mp hs
  refine (UpperTheory.V.AlgebraTools.Det.gramIff ρ).mpr ⟨g, fun h0 => hg ?_⟩
  have e : (Matrix.of fun a b => (ρ (g a * g b)).trace) = f.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h]
  have e' : (Matrix.of fun a b => (ρ' (g a * g b)).trace) = φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h']
  rw [e, ← RingHom.map_det, map_eq_zero_iff f hf] at h0
  rw [e', ← RingHom.map_det, h0, map_zero]

private theorem lift_surj {G K : Type} [Group G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) :
    Function.Surjective (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ) := by
  have : LinearMap.range (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of K G g, by simp⟩
  exact LinearMap.range_eq_top.1 this

private theorem conj_of_trace {G K : Type} [Group G] [Field K] {n : ℕ} (ρ₁ ρ₂ : G →* Matrix (Fin n) (Fin n) K)
    (h₂ : Submodule.span K (Set.range ρ₂) = ⊤) (hf : ∀ g, (ρ₁ g).trace = (ρ₂ g).trace) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ ∀ g, ρ₁ g * P = P * ρ₂ g := by
  have h₁ := span_of_trace (RingHom.id K) Function.injective_id (RingHom.id K) (fun g => (ρ₁ g).trace) ρ₁ ρ₂
    (fun _ => rfl) hf h₂
  set R₁ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₁ with hR₁
  set R₂ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₂ with hR₂
  have s₂ : Function.Surjective R₂ := lift_surj ρ₂ h₂
  have e1 : ∀ g, R₁ (MonoidAlgebra.of K G g) = ρ₁ g := fun g => by simp [hR₁]
  have e2 : ∀ g, R₂ (MonoidAlgebra.of K G g) = ρ₂ g := fun g => by simp [hR₂]
  have hf' : ∀ a, (R₁ a).trace = (R₂ a).trace := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g => rw [e1, e2, hf]
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb]
    | smul c a ha => simp only [map_smul, Matrix.trace_smul, ha]
  have hker : ∀ a, R₂ a = 0 → R₁ a = 0 := by
    intro a ha
    refine zero_of_trace ρ₁ h₁ _ fun g => ?_
    rw [← e1, ← map_mul, hf', map_mul, ha, mul_zero, Matrix.trace_zero]
  let φ₀ := RingHom.liftOfSurjective R₂.toRingHom s₂ ⟨R₁.toRingHom, fun a ha => hker a ha⟩
  have hφ₀ : ∀ a, φ₀ (R₂ a) = R₁ a := fun a => RingHom.liftOfSurjective_comp_apply R₂.toRingHom s₂ _ a
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K :=
    ⟨φ₀, fun c => by
      have := hφ₀ (algebraMap K _ c)
      rwa [AlgHom.commutes, AlgHom.commutes] at this⟩
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom φ
  refine ⟨J, J.isUnit, fun g => ?_⟩
  have h1 := hJ (R₂ (MonoidAlgebra.of K G g))
  have e : φ (R₂ (MonoidAlgebra.of K G g)) = R₁ (MonoidAlgebra.of K G g) := hφ₀ _
  rwa [e, e1, e2] at h1

private theorem alt_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (P A B : Matrix (Fin 2) (Fin 2) K) (hP : IsUnit P)
    (hs : Pᵀ = -P) (h : Bᵀ * P = P * A) : A + B = A.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have d : ∀ i, P i i = 0 := fun i => by
    have := congrFun (congrFun hs i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    exact (mul_eq_zero.1 (by linear_combination this : 2 * P i i = 0)).resolve_left h2
  have o : P 1 0 = -P 0 1 := congrFun (congrFun hs 0) 1
  have u : P 0 1 ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero
    rw [Matrix.det_fin_two, d, d, o] at this
    intro h0
    simp [h0] at this
  have k := fun i j => congrFun (congrFun h i) j
  have k00 := k 0 0
  have k01 := k 0 1
  have k10 := k 1 0
  have k11 := k 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, d, o] at k00 k01 k10 k11
  ext i j
  apply mul_left_cancel₀ u
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two, -mul_eq_mul_left_iff, -mul_eq_zero]
  · linear_combination k01
  · linear_combination k11
  · linear_combination -k00
  · linear_combination -k10

private theorem not_alt {G K : Type} [Group G] [Field K] (h2 : (2 : K) ≠ 0) (ρ : G →* Matrix (Fin 2) (Fin 2) K)
    (hs : Submodule.span K (Set.range ρ) = ⊤)
    (h : ∀ g x, (ρ x * ρ g).trace + (ρ x * (Jmat K 2 * (ρ g)ᵀ * Jmat K 2)).trace = (ρ g).trace * (ρ x).trace) :
    False := by
  have h1 : ∀ g, ρ g 0 1 = 0 := fun g => by
    have := zero_of_trace ρ hs (ρ g + Jmat K 2 * (ρ g)ᵀ * Jmat K 2 - (ρ g).trace • 1) fun x => by
      rw [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, h, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, smul_eq_mul, sub_self]
    have e := congrFun (congrFun this 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Jmat, Fin.rev] at e
    exact (mul_eq_zero.1 (by linear_combination e : 2 * ρ g 0 1 = 0)).resolve_left h2
  have := zero_of_trace ρ hs (Matrix.single 1 0 1) fun g => by simp [Matrix.trace_mul_single, h1]
  simpa using congrFun (congrFun this 1) 0

theorem UpperTheory.V.Fr.of_trace :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [IsAlgClosed K] [Algebra C K], Function.Injective (algebraMap C K) → ∀ (r : F.G0 →* Matrix (Fin n) (Fin n) K) (t : F.G0 → C) (χ : ∀ v, Fin n → F.Gv v →* Cˣ), IsTr O F n t → (∀ g, algebraMap C K (t g) = (r g).trace) → (∀ g, t (F.star g) = t g) → IsPsi O F n (fun v i g => (χ v i g : C)) → (∀ v g h, (r h * ordProd (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g).trace = 0) → ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (φ : C →+* K') (ρ' : NRep F n K'), MatIrr ⊤ ρ'.r → (∀ g, φ (t g) = (ρ'.r g).trace) → ∃ (ρ : NRep F n K) (h : GL (Fin n) K), (∀ g, ρ.r g = h * r g * h⁻¹) ∧ (∀ v i g, (ρ.ψ v i g : K) = algebraMap C K (χ v i g)) ∧ Integral O C ρ ∧ MatIrr ⊤ ρ.r := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r t χ ht htr hst hχ hord K' _ _ φ ρ' hirr hφ
  obtain ⟨ss, sm, -, -, -⟩ := UpperTheory.V.Fr.star hF
  have h2C : IsUnit (2 : C) := by
    by_contra hn2
    have h0 := (res_eq_zero_iff O C 2).2 hn2
    rw [map_ofNat] at h0
    have := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have h2K : (2 : K) ≠ 0 := by simpa [map_ofNat] using (h2C.map (algebraMap C K)).ne_zero
  have h2K' : (2 : K') ≠ 0 := by simpa [map_ofNat] using (h2C.map φ).ne_zero
  have hs' : Submodule.span K' (Set.range ρ'.r) = ⊤ :=
    (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ'.r).1 fun N hN => hirr N fun g _ => hN g
  have hs := span_of_trace (algebraMap C K) hinj φ t r ρ'.r htr hφ hs'
  have s1 : F.star 1 = 1 := by simp [Frame.star]
  let r' : F.G0 →* Matrix (Fin n) (Fin n) K :=
    { toFun := fun g => (r (F.star g))ᵀ
      map_one' := by rw [s1, map_one, Matrix.transpose_one]
      map_mul' := fun g h => by rw [sm, map_mul, Matrix.transpose_mul] }
  obtain ⟨P, hP, hPr⟩ := conj_of_trace r' r hs fun g => by
    show (r (F.star g))ᵀ.trace = _
    rw [Matrix.trace_transpose, ← htr, ← htr, hst]
  replace hPr : ∀ g, (r (F.star g))ᵀ * P = P * r g := hPr
  have sc : ∀ g, F.star g * F.conj g = 1 := fun g => by rw [Frame.star, ← map_mul, inv_mul_cancel, map_one]
  have hform : ∀ g, (r g)ᵀ * P * r (F.conj g) = P := fun g => by
    have := hPr (F.star g)
    rw [ss] at this
    rw [this, Matrix.mul_assoc, ← map_mul, sc, map_one, Matrix.mul_one]
  have cc : ∀ g, F.conj (F.conj g) = g := fun g => by
    have := ss g
    simpa only [Frame.star, map_inv, inv_inv] using this
  have hsym : Pᵀ = P := by
    refine (UpperTheory.V.AlgebraTools.Det.signLemma r F.conj (fun _ => 1) P hs cc (fun _ => rfl) hP
      fun g => by rw [hform, one_smul]).resolve_right fun ha => ?_
    rcases hn with rfl | rfl
    · refine not_alt h2K' ρ'.r hs' fun g x => ?_
      rw [← ρ'.pol, ← map_mul, ← map_mul, ← hφ, ← hφ, ← hφ, ← hφ, ← map_add, ← map_mul]
      congr 1
      apply hinj
      rw [map_add, map_mul, htr, htr, htr, htr, map_mul, map_mul, ← Matrix.trace_add, ← Matrix.mul_add,
        alt_two h2K P _ _ hP ha (hPr g), Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    · have hd := congrArg Matrix.det ha
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hd
      exact mul_ne_zero h2K ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero (by linear_combination hd)
  obtain ⟨ρ, h, h1, h2, h3⟩ := UpperTheory.V.Fr.of_form hF hn C K hinj r P t χ hP hsym hform ht htr hχ
    fun v g => zero_of_trace r hs _ (hord v g)
  refine ⟨ρ, h, h1, h2, h3, fun N hN => ?_⟩
  refine (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ.r).2 ?_ N fun g => hN g trivial
  refine span_of_trace (algebraMap C K) hinj φ t ρ.r ρ'.r (fun g => ?_) hφ hs'
  rw [h1, htr, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
