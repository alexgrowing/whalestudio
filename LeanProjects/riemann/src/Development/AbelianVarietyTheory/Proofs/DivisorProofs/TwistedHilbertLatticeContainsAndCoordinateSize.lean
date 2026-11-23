import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.TwistSize

theorem intVec_mem_std {F : Type} [Field F] [NumberField F] (z : Fin 2 → ℤ) :
    (fun j ↦ ((z j : ℤ) : F)) ∈ stdLat F := by
  rw [stdLat, Submodule.mem_pi]
  intro j _
  exact Submodule.mem_one.2 ⟨(z j : 𝓞 F), by simp⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ N n L α ρ₀ hLs hnL hL hN
  have hR := GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam
  have hZ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  let A : Matrix (Fin 2) (Fin 2) ℤ := (α : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
  have hAα : A.map (Int.cast : ℤ → ZMod N) = (α : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    ext i j; simp [A, ZMod.intCast_cast, ZMod.cast_id']
  have hI := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A · hLs)
  rw [← hAα]
  refine ⟨?_, ?_⟩
  · let B : Matrix (Fin 2) (Fin 2) ℤ :=
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
    have h1 : ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmod : ∀ i j, (((B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod N) = 0 := by
      intro i j
      have h2 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_apply] at h2
      rw [Int.cast_sub, Matrix.mul_apply, Int.cast_sum, Matrix.one_apply]
      rw [Matrix.one_apply] at h2
      simp only [Int.cast_mul, B, A, Matrix.map_apply, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [h2]; split_ifs <;> simp
    have hdv : ∀ i j, (N : ℤ) ∣ (B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (hmod i j)
    choose D hD using hdv
    have hy : (fun j ↦ (n : F) * (B 1 j : F)) ∈ L := by
      have := hnL _ (intVec_mem_std (fun j ↦ B 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    have hw : (fun j ↦ -((n : F) * (D 1 j : F))) ∈ stdLat F := by
      have := Submodule.smul_mem (stdLat F) (-(n : 𝓞 F)) (intVec_mem_std (fun j ↦ D 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    refine (hI _).2 ⟨_, hy, _, hw, ?_⟩
    have hBA : ∀ j, (B 1 0 : F) * (A 0 j : F) + (B 1 1 : F) * (A 1 j : F) = (if (1 : Fin 2) = j then 1 else 0) + (N : F) * (D 1 j : F) := by
      intro j
      have := congrArg (Int.cast : ℤ → F) (hD 1 j)
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this
      split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linear_combination this
    ext j
    fin_cases j
    · have := hBA 0
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
    · have := hBA 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
  · intro v hv i
    obtain ⟨y, hy, w, hw, rfl⟩ := (hI v).1 hv
    have hw0 : w 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [stdLat, Submodule.mem_pi] at hw; exact hw 0 (Set.mem_univ _)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hw0
    have hint : Sz l lam 0 ((i (w 0) : ℝ) : ℂ) := by
      refine hZ.1 1 _ (Nat.Prime.not_dvd_one (Fact.out)) ?_
      rw [Nat.cast_one, one_mul, ← hr]
      exact map_isIntegral_int ((Complex.ofRealHom.comp i).comp (algebraMap (𝓞 F) F)) (RingOfIntegers.isIntegral r)
    have heq : ((i ((Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) 0) : ℝ) : ℂ) =
        ((i (y 0) : ℝ) : ℂ) * ((A 0 0 : ℤ) : ℂ) + ((i (y 1) : ℝ) : ℂ) * ((A 1 0 : ℤ) : ℂ) + (N : ℂ) * ((i (w 0) : ℝ) : ℂ) := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [heq]
    have p1 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 0 i) (hR.2.2.2.2.1 (A 0 0))
    have p2 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 1 i) (hR.2.2.2.2.1 (A 1 0))
    have p3 := hR.2.2.1 ρ₀ 0 _ _ hN hint
    rw [add_zero] at p1 p2 p3
    exact (hR.2.1 _ _ _ (hR.2.1 _ _ _ p1 p2).1 p3).1

end GlobalTheory.HilbFam.TwistSize
