import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.LfacDenominatorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCornerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidanceStatement

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

namespace GlobalTheory.SiegelDense

theorem prod_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {ι : Type} (s : Finset ι) (a b : ι → R) :
    ∏ i ∈ s, (e * a i + (1 - e) * b i) = e * ∏ i ∈ s, a i + (1 - e) * ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih]
    linear_combination (a i * ∏ j ∈ s, a j - a i * ∏ j ∈ s, b j - b i * ∏ j ∈ s, a j + b i * ∏ j ∈ s, b j) * he

theorem det_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {m : Type} [Fintype m] [DecidableEq m]
    (A B : Matrix m m R) : (e • A + (1 - e) • B).det = e * A.det + (1 - e) * B.det := by
  simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [prod_idem he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h] <;> ring

theorem isUnit_mix {R : Type} [CommRing R] {e : R} (he : e * e = e) {a b : R} (ha : IsUnit (e * a + (1 - e)))
    (hb : IsUnit b) : IsUnit (e * a + (1 - e) * b) := by
  obtain ⟨u, rfl⟩ := hb
  have h1 : e * a + (1 - e) * (u : R) = (e * a + (1 - e)) * (e + (1 - e) * (u : R)) := by
    linear_combination (-a + a * (u : R) + 1 - (u : R)) * he
  have h2 : IsUnit (e + (1 - e) * (u : R)) := by
    refine isUnit_iff_exists_inv.mpr ⟨e + (1 - e) * ((u⁻¹ : Rˣ) : R), ?_⟩
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination (2 - (u : R) - ((u⁻¹ : Rˣ) : R)) * he + (1 - e) ^ 2 * hu
  rw [h1]
  exact ha.mul h2

theorem mix_corner {R : Type} [CommRing R] {n : ℕ} (e : R) (he : e * e = e) (A : Matrix (Fin n) (Fin n ⊕ Fin n) R)
    (B D' : Matrix (Fin n ⊕ Fin n) (Fin n) R) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (y : Matrix (Fin n) (Fin n) R)
    (hAB : A * B = (2 : R) • 1) (hAD : A * D' = 0) :
    A * (e • G + (1 - e) • 1) * B + A * (e • G + (1 - e) • 1) * D' * (e • y) =
      e • (A * G * B + A * G * D' * y) + (1 - e) • ((2 : R) • (1 : Matrix (Fin n) (Fin n) R)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hAB, hAD,
    Matrix.zero_mul, smul_zero, add_zero, smul_smul, he, smul_add]
  simp only [Matrix.mul_assoc]
  abel

theorem approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀),
    ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀,
      (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) +
          (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧
      Tendsto q atTop (𝓝 g) :=
  GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary

theorem unip : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R)
    {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 →
    ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) =
        diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R,
        Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) *
            Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) =
          Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h *
              Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) +
            Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x :=
  GlobalTheory.T.siegelUnipotent_antidiagonal_corner

theorem avoid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)),
    (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω),
      φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) +
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) :=
  GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value

theorem exists_corner : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
      ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) :=
  GlobalTheory.T.exists_corner_unit_of_right_inverse'

theorem descend : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R),
    (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R),
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ),
      (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det →
      ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) →
        ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) :=
  GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance'

theorem dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ g : UG (cA σ) (dbl (incM F J)), g ∈ closure {h : UG (cA σ) (dbl (incM F J)) | ∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧ IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det} := by
  intro F E _ _ _ _ _ σ hσ n J ε hJ hdet g
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : AE F E) := (Invertible.map (algebraMap F (AE F E)) (2 : F)).copy 2 (map_ofNat (algebraMap F (AE F E)) 2).symm
  obtain ⟨q, hq, hlim⟩ := approx F E σ (dbl (incM F J)) g
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun S => ?_)
  have he : algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
      = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := by
    rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hce : cA σ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := (cA σ).commutes _
  have hav := avoid F E S

  have hNtN : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [Matrix.fromCols_mul_fromRows, two_smul]; simp
  have hNtD : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = 0 := by
    rw [diagCols, Matrix.fromCols_mul_fromRows]; simp
  have hNN : Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) +
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [diagCols, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]

  obtain ⟨x₀, hx₀⟩ := exists_corner (F := F) _ he hav
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    (by
      have hg : (g.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
          ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = 1 := g.1.mul_inv
      rw [show ∀ (A : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E)) (B : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))
          (N₁ N₂ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (T₁ T₂ : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E))
          (G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (k : AE F E),
          A * G * N₁ * (k • (T₁ * H * B)) + A * G * N₂ * (k • (T₂ * H * B)) = k • (A * (G * ((N₁ * T₁ + N₂ * T₂) * (H * B)))) from
        fun A B N₁ N₂ T₁ T₂ G H k => by simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, smul_add]]
      rw [hNN, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc (g.1.1 : Matrix _ _ _), hg,
        Matrix.one_mul, hNtN, smul_smul, smul_smul,
        show ((⅟2 * ⅟2 : AE F E) * 2 * 2) = 1 by rw [mul_assoc (⅟2 : AE F E) (⅟2) 2, invOf_mul_self, mul_one, invOf_mul_self],
        one_smul])

  obtain ⟨y, hy⟩ : ∃ y : E, σ y ≠ y := by
    by_contra h
    push_neg at h
    exact GlobalTheory.HeckeObjectExamples.sigma_ne_id hσ (AlgHom.ext h)
  have hinv : ∀ z, σ (σ z) = z := GlobalTheory.HeckeObjectExamples.sigma_invol hσ
  have hcincl : ∀ z : E, cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := fun z => by
    change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] z) = (1 : AF F) ⊗ₜ[F] σ z
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hρu : IsUnit (inclR (F := F) (AF F) (y - σ y)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hy))).map _
  have hcρ : (cA σ).toRingHom (inclR (F := F) (AF F) (y - σ y)) = -inclR (F := F) (AF F) (y - σ y) := by
    change cA σ _ = _
    rw [hcincl, map_sub, hinv, ← map_neg, neg_sub]
  have hc2 : ∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r := fun r => by
    change cA σ (cA σ r) = r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simp [cA, Algebra.TensorProduct.map_tmul, hinv]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hcF : ∀ t : F, (cA σ).toRingHom (algebraMap F (AE F E) t) = algebraMap F (AE F E) t := fun t => by
    change cA σ _ = _
    rw [IsScalarTower.algebraMap_apply F (AF F) (AE F E), AlgHom.commutes]
  have hJm : ((incM F J).map (cA σ).toRingHom)ᵀ = ((ε : ℤ) : AE F E) • incM F J := by
    ext i j
    change cA σ (inclR (F := F) (AF F) (J j i)) = ((ε : ℤ) : AE F E) * inclR (F := F) (AF F) (J i j)
    rw [hcincl, hJ, map_mul, map_intCast]
  have hJdet : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  obtain ⟨x, hxV, hx⟩ := descend (F := F) (cA σ).toRingHom hc2 hcF _ hav _ hρu hcρ (incM F J) ε hJm hJdet _ _ x₀ hx₀

  have hxV' : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x)ᵀ * incM F J +
      incM F J * (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) = 0 := by
    have h1 : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x.map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hce]
    rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    rw [show x.map (cA σ) = x.map (cA σ).toRingHom from rfl, hxV, smul_zero]
  obtain ⟨p, hpD, hcorner⟩ := unip (cA σ) (incM F J) _ hxV'
  refine ⟨p, 1, hpD, ?_⟩
  have hmul : ((q S * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = (q S).1.1 * p.1.1 := rfl
  rw [hmul, hcorner, hq S]
  have hk := mix_corner (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) he
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (diagCols (Fin n)) (g.1.1) x hNtN hNtD
  erw [hk]
  rw [det_idem he, Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_mix he hx ((isUnit_of_invertible (2 : AE F E)).pow _)

end GlobalTheory.SiegelDense
