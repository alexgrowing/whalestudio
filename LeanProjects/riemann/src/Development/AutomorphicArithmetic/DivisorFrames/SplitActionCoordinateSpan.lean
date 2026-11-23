import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

section SlopeTestRemainingChoices
open Matrix TensorProduct

private theorem product_shift_mulVec_eigen {T O S : Type} [CommRing T] {g : ℕ} (M : O → Matrix (Fin g) (Fin g) T)
    (a : O → T) (b : S → O → T) (w : Fin g → T) (hw : ∀ c, (M c).mulVec w = a c • w)
    (P : List (S × O)) :
    (P.map fun p => M p.2 - Matrix.scalar (Fin g) (b p.1 p.2)).prod.mulVec w
      = (P.map fun p => a p.2 - b p.1 p.2).prod • w := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Matrix.sub_mulVec, hw, mul_comm, mul_smul, sub_smul]
    congr 2
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem product_eigen_shift_eq_zero {K O S : Type} [Field K] [CommRing O] {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) K) (χ : S → (O →+* K)) (h : GlobalTheory.VB.IsSplitBy χ)
    (P : List (S × O)) (hP : ∀ j, ∃ c, (j, c) ∈ P) :
    (P.map fun p => ρ p.2 - Matrix.scalar (Fin g) (χ p.1 p.2)).prod = 0 := by
  let Φ : K ⊗[ℤ] O →ₐ[K] Matrix (Fin g) (Fin g) K :=
    Algebra.TensorProduct.lift (Algebra.ofId K _) ρ.toIntAlgHom
      fun x y => Algebra.commutes x _
  have h0 : (P.map fun p => ((1 : K) ⊗ₜ[ℤ] p.2 - (χ p.1 p.2) ⊗ₜ[ℤ] (1 : O) : K ⊗[ℤ] O)).prod = 0 := by
    apply h.1
    rw [map_zero, map_list_prod]
    funext j
    obtain ⟨c, hc⟩ := hP j
    have := map_list_prod (Pi.evalRingHom (fun _ : S => K) j)
      (List.map (GlobalTheory.VB.splitMap χ) (P.map fun p => ((1 : K) ⊗ₜ[ℤ] p.2 - (χ p.1 p.2) ⊗ₜ[ℤ] (1 : O) : K ⊗[ℤ] O)))
    refine this.trans ?_
    rw [Pi.zero_apply, List.prod_eq_zero_iff]
    simp only [List.map_map, List.mem_map]
    exact ⟨(j, c), hc, by simp⟩
  have := congrArg Φ h0
  rw [map_zero, map_list_prod, List.map_map] at this
  rw [← this]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  have hΦ : ∀ (x : K) (y : O), Φ (x ⊗ₜ[ℤ] y) = Matrix.scalar (Fin g) x * ρ y := fun _ _ => rfl
  simp only [Function.comp_apply, map_sub, hΦ, map_one, one_mul, mul_one]

private theorem dual_basis_coordinates_sum {T : Type} [CommRing T] {g n : ℕ} (B C : Matrix (Fin g) (Fin g) T)
    (hBC : B * C = 1) (e : Fin n ↪ Fin g) (a : Fin n → T) (j : Fin g) :
    (Cᵀ *ᵥ (∑ m, a m • B (e m))) j = ∑ m, if e m = j then a m else 0 := by
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_transpose, Pi.smul_apply]
  have : (B (e m) ᵥ* C) j = (B * C) (e m) j := rfl
  rw [this, hBC, Matrix.one_apply]
  split_ifs <;> simp

private theorem vector_expand_in_complementary_basis {T : Type} [CommRing T] {g n : ℕ} (B C : Matrix (Fin g) (Fin g) T)
    (hCB : C * B = 1) (e : Fin n ↪ Fin g) (x : Fin g → T)
    (hx : ∀ j, j ∉ Set.range e → (Cᵀ *ᵥ x) j = 0) :
    x = ∑ m, (Cᵀ *ᵥ x) (e m) • B (e m) := by
  classical
  have h1 : x = ∑ j, (Cᵀ *ᵥ x) j • B j := by
    have : x = (x ᵥ* C) ᵥ* B := by rw [Matrix.vecMul_vecMul, hCB, Matrix.vecMul_one]
    rw [Matrix.mulVec_transpose]
    conv_lhs => rw [this]
    ext i
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  conv_lhs => rw [h1]
  rw [← Finset.sum_map Finset.univ e fun j => (Cᵀ *ᵥ x) j • B j]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
  rw [hx j (by simpa using hj), zero_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.split_action_coordinate_span :
    ∀ (O R K S : Type) [CommRing O] [CommRing R] [Field K] [Fintype S] (ι : R →+* K), Function.Injective ι → ∀ (g n : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) R) (χ : S → (O →+* R)) (τ : S), GlobalTheory.VB.IsSplitBy (fun σ => ι.comp (χ σ)) → (∀ σ, σ ≠ τ → ∃ c, IsUnit (χ τ c - χ σ c)) → ∀ (v : Fin n → Fin g → R) (e : Fin n ↪ Fin g) (B : Matrix (Fin g) (Fin g) R), IsUnit B.det → (∀ m, B (e m) = v m) → (∀ cf : Fin g → K, (∀ c, ((ρ c).map ι).mulVec cf = ι (χ τ c) • cf) ↔ cf ∈ Submodule.span K (Set.range fun m j => ι (v m j))) → ∀ (R' : Type) [CommRing R'] (α : R →+* R'), (∀ m c, ((ρ c).map α).mulVec (fun j => α (v m j)) = α (χ τ c) • fun j => α (v m j)) ∧ ∀ cf : Fin g → R', (∀ c, ((ρ c).map α).mulVec cf = α (χ τ c) • cf) → ∃! a : Fin n → R', cf = ∑ m, a m • fun j => α (v m j) := by
  intro O R K S _ _ _ _ ι hι g n ρ χ τ hs hu v e B hB hv hK R' _ α
  classical
  refine ⟨fun m c => ?_, fun cf hcf => ?_⟩
  · have h1 := (hK (fun j => ι (v m j))).2 (Submodule.subset_span ⟨m, rfl⟩) c
    have h2 : (ρ c).mulVec (v m) = χ τ c • v m := by
      funext j
      apply hι
      have := congrFun h1 j
      rw [RingHom.map_mulVec]
      simpa [Function.comp_def] using this
    funext j
    have := congrArg α (congrFun h2 j)
    rw [RingHom.map_mulVec] at this
    simpa [Function.comp_def] using this
  · have hu' : ∀ σ, ∃ c, σ ≠ τ → IsUnit (χ τ c - χ σ c) := fun σ => by
      by_cases h : σ = τ
      · exact ⟨0, fun h' => absurd h h'⟩
      · obtain ⟨c, hc⟩ := hu σ h
        exact ⟨c, fun _ => hc⟩
    choose c hc using hu'
    let P : List (S × O) := (Finset.univ.erase τ).toList.map fun σ => (σ, c σ)
    let η : Matrix (Fin g) (Fin g) R :=
      (P.map fun p => ρ p.2 - Matrix.scalar (Fin g) (χ p.1 p.2)).prod
    have hη : ∀ (T : Type) [CommRing T] (β : R →+* T), η.map β =
        (P.map fun p => (ρ p.2).map β - Matrix.scalar (Fin g) (β (χ p.1 p.2))).prod := by
      intro T _ β
      have := map_list_prod (β.mapMatrix (m := Fin g))
        (P.map fun p => ρ p.2 - Matrix.scalar (Fin g) (χ p.1 p.2))
      refine this.trans ?_
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      rw [Function.comp_apply, map_sub]
      simp [Matrix.scalar_apply, Matrix.diagonal_map]
    have hBC : ∀ (T : Type) [CommRing T] (β : R →+* T), B.map β * (B⁻¹).map β = 1 := by
      intro T _ β
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv B hB, Matrix.map_one _ (map_zero β) (map_one β)]
    have hCB : ∀ (T : Type) [CommRing T] (β : R →+* T), (B⁻¹).map β * B.map β = 1 := by
      intro T _ β
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul B hB, Matrix.map_one _ (map_zero β) (map_one β)]
    have hrow : ∀ (T : Type) [CommRing T] (β : R →+* T) (m : Fin n),
        (fun j => β (v m j)) = B.map β (e m) := by
      intro T _ β m
      rw [← hv m]; rfl
    have hηK : ∀ (w : Fin g → K) (d : O), ((ρ d).map ι).mulVec ((η.map ι).mulVec w)
        = ι (χ τ d) • (η.map ι).mulVec w := by
      intro w d
      have h0 := product_eigen_shift_eq_zero ((ι.mapMatrix (m := Fin g)).comp ρ) (fun σ => ι.comp (χ σ)) hs
        ((τ, d) :: P) (fun j => by
          by_cases h : j = τ
          · exact ⟨d, by simp [h]⟩
          · exact ⟨c j, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, by simp [h], rfl⟩)⟩)
      rw [List.map_cons, List.prod_cons] at h0
      have h1 : ((ρ d).map ι - Matrix.scalar (Fin g) (ι (χ τ d))) * η.map ι = 0 := by
        rw [hη]; exact h0
      have h2 := congrArg (fun M => Matrix.mulVec M w) h1
      simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.zero_mulVec, sub_eq_zero] at h2
      rw [h2]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hN : ∀ j, j ∉ Set.range e → ∀ i, ((B⁻¹).transpose * η) j i = 0 := by
      intro j hj i
      apply hι
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
        ((hK _).1 (hηK (Pi.single i 1)))
      simp only [hrow] at ha
      have h1 := dual_basis_coordinates_sum _ _ (hBC K ι) e a j
      rw [ha, Finset.sum_eq_zero (fun m _ => if_neg fun h => hj ⟨m, h⟩), Matrix.mulVec_mulVec,
        ← Matrix.transpose_map, ← Matrix.map_mul, Matrix.mulVec_single_one] at h1
      rw [map_zero]
      exact h1
    have hunit : IsUnit (P.map fun p => α (χ τ p.2) - α (χ p.1 p.2)).prod := by
      refine List.prod_isUnit fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hp
      rw [← map_sub]
      exact (hc σ (by simpa using hσ)).map α
    have hE := product_shift_mulVec_eigen (fun d => (ρ d).map α) (fun d => α (χ τ d)) (fun σ d => α (χ σ d))
      cf hcf P
    rw [← hη] at hE
    have hx : ∀ j, j ∉ Set.range e → (((B⁻¹).map α).transpose.mulVec cf) j = 0 := by
      intro j hj
      have h1 : (((B⁻¹).map α).transpose.mulVec ((η.map α).mulVec cf)) j = 0 := by
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_map, ← Matrix.map_mul]
        simp [Matrix.mulVec, dotProduct, hN j hj]
      rw [hE, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
      exact hunit.mul_right_eq_zero.1 h1
    simp only [hrow]
    refine ⟨fun m => (((B⁻¹).map α).transpose.mulVec cf) (e m),
      vector_expand_in_complementary_basis _ _ (hCB R' α) e cf hx, fun a ha => ?_⟩
    funext m
    rw [ha, dual_basis_coordinates_sum _ _ (hBC R' α) e a (e m)]
    simp
