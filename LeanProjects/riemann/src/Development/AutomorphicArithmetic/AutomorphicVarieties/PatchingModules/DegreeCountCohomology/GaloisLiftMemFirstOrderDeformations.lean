import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Gen

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}

private theorem mem_blkMat_iff_mem_of_same_block_and_mem_off {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ blkMat n a V₁ V₂ ↔ ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₁) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ V₂) :=
  Iff.rfl

private theorem blk_tr {V₁ V₂ : Submodule A R} {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ blkMat n a V₁ V₂) :
    Zᵀ ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hZ ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hZ j i
  exact ⟨fun h => h1 h.symm, fun h => h2 (fun h' => h h'.symm)⟩

private def Act (U₁ U₂ V₁ V₂ : Submodule A R) : Prop :=
  (∀ u ∈ U₁, ∀ v ∈ V₁, u * v ∈ V₁) ∧ (∀ u ∈ U₁, ∀ v ∈ V₂, u * v ∈ V₂) ∧
    (∀ u ∈ U₂, ∀ v ∈ V₁, u * v ∈ V₂) ∧ (∀ u ∈ U₂, ∀ v ∈ V₂, u * v ∈ V₁)

private theorem blk_mul {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) : P * Z ∈ blkMat n a V₁ V₂ := by
  rw [mem_blkMat_iff_mem_of_same_block_and_mem_off] at hP hZ ⊢
  obtain ⟨h11, h12, h21, h22⟩ := H
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · exact h11 _ ((hP i k).1 hik) _ ((hZ k j).1 (hik.symm.trans hij))
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hik (hij.trans h.symm)
      exact h22 _ ((hP i k).2 hik) _ ((hZ k j).2 hkj)
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hkj : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun h => hij (hik.trans h)
      exact h12 _ ((hP i k).1 hik) _ ((hZ k j).2 hkj)
    · have hkj : ((k : ℕ) < a ↔ (j : ℕ) < a) := by tauto
      exact h21 _ ((hP i k).2 hik) _ ((hZ k j).1 hkj)

private theorem blk_sand {U₁ U₂ V₁ V₂ : Submodule A R} (H : Act U₁ U₂ V₁ V₂) {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : P ∈ blkMat n a U₁ U₂) (hQ : Q ∈ blkMat n a U₁ U₂) (hZ : Z ∈ blkMat n a V₁ V₂) :
    P * Z * Q ∈ blkMat n a V₁ V₂ := by
  have h1 := blk_mul H hP hZ
  have h2 := blk_tr (blk_mul H (blk_tr hQ) (blk_tr h1))
  simpa [Matrix.transpose_mul] using h2

private theorem alg_smul_mem {V : Submodule A (Matrix (Fin n) (Fin n) R)} (c : A) {Z : Matrix (Fin n) (Fin n) R}
    (hZ : Z ∈ V) : algebraMap A R c • Z ∈ V := by
  rw [algebraMap_smul]
  exact V.smul_mem c hZ

end Gen

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ}

private theorem ep_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep j = 0 := rfl

private theorem ep'_algebraMap_eq_zero (c : A) (j : Fin g) : (algebraMap A (DD X g) c).ep' j = 0 := rfl

private theorem eta_algebraMap_eq_zero (c : A) : (algebraMap A (DD X g) c).eta = 0 := rfl

private theorem mem_part {p q r s : Bool} {y : DD X g} : y ∈ ddPart A X g p q r s ↔
    (p = false → y.a = 0) ∧ (q = false → ∀ j, y.ep j = 0) ∧ (r = false → ∀ j, y.ep' j = 0) ∧ (s = false → y.eta = 0) := by
  show ((p = false → y.a = 0) ∧ (q = false → y.ep = 0) ∧ (r = false → y.ep' = 0) ∧ (s = false → y.eta = 0)) ↔ _
  simp only [funext_iff, Pi.zero_apply]

private theorem act1 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g true false false false) (ddPart A X g false true false false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act1s : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false false true) (ddPart A X g false false true false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

private theorem act2 : Act (ddPart A X g true false false false) (ddPart A X g false true false false)
    (ddPart A X g false false true false) (ddPart A X g false false false true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro u hu v hv <;> rw [mem_part] at hu hv ⊢ <;> simp_all

end Parts

private theorem galois_lift_mem_first_order_deformations {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hP : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · have hκ : ∀ m, k.κ m g i j = 0 := fun m => by
        have hm := ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 ((k.mem m).1 g)) i j).1 h
        simpa using hm
      rw [mem_part]
      by_cases hij : i = j
      · subst hij
        simp [Matrix.one_apply, DD.epM, hκ]
      · simp [hij, Matrix.one_apply, DD.epM, hκ]
    · have hne : i ≠ j := by
        rintro rfl
        exact h Iff.rfl
      rw [mem_part]
      simp [hne, Matrix.one_apply, DD.epM]
  have hZ : x.ρX (DD X k.g) g ∈ W1 n x.A X k.g x.a := by
    show _ ∈ blkMat n x.a (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false)
    refine mem_blkMat_iff_mem_of_same_block_and_mem_off.2 (fun i j => ⟨fun h => ?_, fun h => ?_⟩)
    · rw [mem_part]
      simp [NP.ρX, ep_algebraMap_eq_zero, ep'_algebraMap_eq_zero, eta_algebraMap_eq_zero]
    · have h0 : (mat x.ρ) g i j = 0 := by
        simpa using ((mem_blkMat_iff_mem_of_same_block_and_mem_off.1 (x.blk g)) i j).2 h
      rw [mem_part]
      simp [NP.ρX, h0]
  exact blk_mul act1 hP hZ

theorem UpperTheory.V.Pa.ok1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W1 n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧ AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (W2 n x.A X k.g x.a) := by
  intro l _ L G G0 h n x k X _ _ χ
  obtain ⟨r1, r2, r3, -, -⟩ := rho1 l G0.frame n x k X
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [Glob.Hom.p₀, GFrame.conj, h.c]
  have key : ∀ V₁ V₂ : Submodule x.A (DD X k.g),
      Act (ddPart x.A X k.g true false false false) (ddPart x.A X k.g false true false false) V₁ V₂ →
      AdOk G.frame (fun g => k.ρ1 X (h.p₀ g)) (fun g => algebraMap x.A (DD X k.g) (χ g)) (blkMat n x.a V₁ V₂) := by
    intro V₁ V₂ H
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show k.ρ1 X (h.p₀ 1) = 1
      rw [map_one]
      exact r1
    · intro a b
      show k.ρ1 X (h.p₀ (a * b)) = k.ρ1 X (h.p₀ a) * k.ρ1 X (h.p₀ b)
      rw [map_mul]
      exact r2 _ _
    · intro g
      refine ⟨Units.map (algebraMap x.A (DD X k.g) : x.A →* DD X k.g)
        ((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))), ?_⟩
      show (k.ρ1 X (h.p₀ g))ᵀ * k.ρ1 X (h.p₀ (G.frame.conj g)) = _
      rw [hconj, r3]
      rfl
    · show algebraMap x.A (DD X k.g) (χ 1) = 1
      simp
    · intro a b
      show algebraMap x.A (DD X k.g) (χ (a * b)) = algebraMap x.A (DD X k.g) (χ a) * algebraMap x.A (DD X k.g) (χ b)
      simp
    · intro g Z hZ
      show algebraMap x.A (DD X k.g) (χ g) • (k.ρ1 X (h.p₀ g) * Z * k.ρ1 X (h.p₀ g⁻¹)) ∈ _
      exact alg_smul_mem _ (blk_sand H (galois_lift_mem_first_order_deformations k X _) (galois_lift_mem_first_order_deformations k X _) hZ)
    · intro Z hZ
      show algebraMap x.A (DD X k.g) (χ G.frame.c) • Zᵀ ∈ _
      exact alg_smul_mem _ (blk_tr hZ)
  exact ⟨key _ _ act1, key _ _ act1s, key _ _ act2⟩
