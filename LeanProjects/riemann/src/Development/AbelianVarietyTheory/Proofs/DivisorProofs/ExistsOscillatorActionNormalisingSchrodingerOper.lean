import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.SchrodOsc

section Sign

variable {N : Type} [Fintype N] [DecidableEq N] (pos : N → Bool)

def signEquiv : N ≃ Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}) :=
  (Equiv.sumCompl (fun n => pos n = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem pos_signEquiv_symm_inl (i : Fin (Fintype.card {n // pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.symm_symm, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin _).symm i).2

theorem pos_signEquiv_symm_inr (j : Fin (Fintype.card {n // ¬ pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inr j)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.symm_symm, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin _).symm j).2

theorem fromBlocks_eq_reindex :
    (fromBlocks 1 0 0 (-1) : Matrix (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}))
      (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      reindex (signEquiv pos) (signEquiv pos) (diagonal fun n => if pos n then 1 else -1) := by
  rw [reindex_apply, submatrix_diagonal_equiv]
  have h1 : (1 : Matrix (Fin (Fintype.card {n // pos n = true})) (Fin (Fintype.card {n // pos n = true})) ℂ) =
      diagonal fun _ => 1 := diagonal_one.symm
  have h2 : (-1 : Matrix (Fin (Fintype.card {n // ¬ pos n = true})) (Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      diagonal fun _ => -1 := by rw [← diagonal_neg, diagonal_one]
  rw [h1, h2, fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | j
  · simp [pos_signEquiv_symm_inl]
  · simp [pos_signEquiv_symm_inr]

end Sign

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def sgn (n : Ix R S × (ι × Ix P Q)) : Bool := linePos (p := P) (q := Q) (r := R) (s := S) (n.2.2, n.1)

theorem lineSign_eq (a : Ix P Q) (b : Ix R S) : lineSign a b = if linePos (a, b) then 1 else -1 := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem Jm_transpose (R S : ℕ) : (Jm R S)ᵀ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, fromBlocks_transpose]

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Jm, Formalism.UG.Jpq, one_apply] <;> split_ifs <;> simp

theorem diagonal_sgn : (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) =
    blockDiagonal fun o : ι × Ix P Q => Jm P Q o.2 o.2 • Jm R S := by
  ext ⟨b, w, a⟩ ⟨b', w', a'⟩
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [diagonal_apply, blockDiagonal_apply, Jm, Formalism.UG.Jpq, sgn, linePos, one_apply, Prod.ext_iff] <;>
    split_ifs <;> simp_all

theorem blockDiagonal_mem (M : ι → Mat R S) (hM : ∀ w, (M w)ᴴ * Jm R S * M w = Jm R S) :
    (blockDiagonal fun o : ι × Ix P Q => M o.1)ᵀ *
        (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) *
        (blockDiagonal fun o : ι × Ix P Q => M o.1).map star =
      diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1 := by
  rw [diagonal_sgn, blockDiagonal_transpose, blockDiagonal_map _ _ (star_zero ℂ), ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end Block

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Hom

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} {G : Type} [Group G]

abbrev lineNum (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) :=
  signEquiv (sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S))

def blockHom (P Q : ℕ) (k : G →* (ι → Mat R S)) :
    G →* Matrix (Ix R S × (ι × Ix P Q)) (Ix R S × (ι × Ix P Q)) ℂ where
  toFun g := blockDiagonal fun o : ι × Ix P Q => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal_one
  map_mul' g g' := by simp [blockDiagonal_mul]

def numHom (P Q : ℕ) (k : G →* (ι → Mat R S)) : G →* Matrix (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}))
      (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true})) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum ι P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (ι → Mat R S)) (g : G) :
    numHom P Q k g = reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)).map star =
      reindex (lineNum ι P Q R S) (lineNum ι P Q R S) ((blockDiagonal fun o : ι × Ix P Q => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal_mem _ (hk g)]

def unitHom (P Q : ℕ) (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)) (hc : Continuous k)
    (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) : Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)
    exact (Continuous.matrix_blockDiagonal (continuous_pi fun (o : ι × Ix P Q) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

end Hom

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def coordOf (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum ι P Q R S (b, (w, a)))

theorem coordOf_add (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum ι P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Ix R S × (ι × Ix P Q) → ℂ := fun n => (if sgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F (b, (w, a)) := by
    intro w a b
    simp only [coordOf, F, star_mul, sgn, lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F (b, (w, a)) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, pos_signEquiv_symm_inl, pos_signEquiv_symm_inr, Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec {G : Type} [Group G] (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S)
    (g : G) (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp [coordOf, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, mul_apply, Finset.mul_sum, ite_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

end Final

end GlobalTheory.SchrodOsc

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem GlobalTheory.SchrodOsc.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.SchrodOsc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.SchrodOsc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add, ← GlobalTheory.SchrodOsc.coordOf_add, hφ, ← GlobalTheory.SchrodOsc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.SchrodOsc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.SchrodOsc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.SchrodOsc.coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : Ix R S × (ι × Ix P Q) => c n.2.1 n.2.2 n.1)
      ((GlobalTheory.SchrodOsc.lineNum ι P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp [GlobalTheory.SchrodOsc.coordOf, h2]
  have h := hω₀ (GlobalTheory.SchrodOsc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.SchrodOsc.coordOf_mulVec, hz] at h
  exact h
