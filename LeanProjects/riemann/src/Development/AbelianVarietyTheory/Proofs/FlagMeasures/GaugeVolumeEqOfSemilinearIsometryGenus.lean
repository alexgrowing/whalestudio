import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.GaugeTransport

section Algebra

variable {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ}

def conjMat (ρ : R' ≃+* R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A * A' = 1) (h2 : A' * A = 1) : Matrix (Fin m) (Fin m) R' ≃* Matrix (Fin n) (Fin n) R where
  toFun g := A * g.map ρ * A'
  invFun h := (A' * h * A).map ρ.symm
  left_inv g := by
    have : A' * (A * g.map ρ * A') * A = g.map ρ := by
      calc _ = (A' * A) * g.map ρ * (A' * A) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    simp only [this]
    ext i j; simp
  right_inv h := by
    have : ((A' * h * A).map ρ.symm).map ρ = A' * h * A := by
      ext i j; exact ρ.apply_symm_apply _
    simp only [this]
    calc _ = (A * A') * h * (A * A') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := by
    have : (g * h).map ρ = g.map ρ * h.map ρ := Matrix.map_mul (f := ρ.toRingHom)
    rw [this]
    calc _ = A * g.map ρ * (A' * A) * h.map ρ * A' := by
          rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_unitary_equiv (ρ : R' ≃+* R) (σ' : R' →+* R') (σ : R →+* R) (hρ : ∀ x, ρ (σ' x) = σ (ρ x))
    (J' : Matrix (Fin m) (Fin m) R') (J : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hJ : Formalism.UG.cT σ A * J * A = J'.map ρ) :
    ∃ T : Formalism.UG.UJ σ' J' ≃* Formalism.UG.UJ σ J, ∀ g,
      ((T g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        A * ((g : GL (Fin m) R') : Matrix (Fin m) (Fin m) R').map ρ * A' := by
  have key : ∀ g : Matrix (Fin m) (Fin m) R',
      Formalism.UG.cT σ A * (Formalism.UG.cT σ (A * g.map ρ * A') * J * (A * g.map ρ * A')) * A =
        (Formalism.UG.cT σ' g * J' * g).map ρ := by
    intro g
    have e1 : (Formalism.UG.cT σ' g * J' * g).map ρ = Formalism.UG.cT σ (g.map ρ) * J'.map ρ * g.map ρ := by
      have a1 : ∀ X Y : Matrix (Fin m) (Fin m) R', (X * Y).map ρ = X.map ρ * Y.map ρ :=
        fun X Y => Matrix.map_mul (f := ρ.toRingHom)
      rw [a1, a1]
      congr 2
      ext i j
      exact hρ _
    have e2 : A * g.map ρ * A' * A = A * g.map ρ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    calc _ = Formalism.UG.cT σ (A * g.map ρ * A' * A) * J * (A * g.map ρ * A' * A) := by
          rw [Formalism.UG.cT_mul σ (A * g.map ρ * A') A]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [e2, e1, ← hJ, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
  have canc : ∀ X Y : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ A * X * A = Formalism.UG.cT σ A * Y * A → X = Y := by
    have : ∀ X : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ A' * (Formalism.UG.cT σ A * X * A) * A' = X := by
      intro X
      calc _ = Formalism.UG.cT σ (A * A') * X * (A * A') := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    intro X Y h
    rw [← this X, h, this]
  let U := Units.mapEquiv (conjMat ρ A A' h1 h2)
  have hU : ∀ g, U g ∈ Formalism.UG.UJ σ J ↔ g ∈ Formalism.UG.UJ σ' J' := by
    intro g
    change Formalism.UG.cT σ (A * g.1.map ρ * A') * J * (A * g.1.map ρ * A') = J ↔
      Formalism.UG.cT σ' g.1 * J' * g.1 = J'
    constructor
    · intro h
      have := key g
      rw [h, hJ] at this
      ext i j
      exact (ρ.injective (congrFun (congrFun this i) j)).symm
    · intro h
      apply canc
      rw [key, h, hJ]
  refine ⟨{ toFun := fun g => ⟨U g, (hU _).2 g.2⟩
            invFun := fun h => ⟨U.symm h, (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact h.2)⟩
            left_inv := fun g => Subtype.ext (U.symm_apply_apply _)
            right_inv := fun g => Subtype.ext (U.apply_symm_apply _)
            map_mul' := fun g h => Subtype.ext (U.map_mul _ _) }, fun g => rfl⟩

theorem stab_and_cong {S : Subring R} {S' : Subring R'} (L : Submodule S (Fin n → R))
    (L' : Submodule S' (Fin m → R')) (Φ : (Fin m → R') →+ (Fin n → R)) (hΦ : Function.Bijective Φ)
    (hL : ∀ w, w ∈ L' ↔ Φ w ∈ L) (g : Matrix (Fin m) (Fin m) R') (G : Matrix (Fin n) (Fin n) R)
    (hg : ∀ w, G *ᵥ Φ w = Φ (g *ᵥ w)) :
    ((∀ w, w ∈ L' ↔ g *ᵥ w ∈ L') ↔ ∀ y, y ∈ L ↔ G *ᵥ y ∈ L) ∧
      ∀ N : ℕ, (∀ w ∈ L', ∃ w' ∈ L', (g - 1) *ᵥ w = (N : R') • w') ↔
        ∀ y ∈ L, ∃ z ∈ L, (G - 1) *ᵥ y = (N : R) • z := by
  refine ⟨?_, fun N => ?_⟩
  · rw [hΦ.2.forall]
    refine forall_congr' fun w => ?_
    rw [hg, ← hL, ← hL]
  · rw [hΦ.2.forall]
    refine forall_congr' fun w => ?_
    rw [← hL, hΦ.2.exists]
    refine imp_congr_right fun _ => exists_congr fun w' => ?_
    rw [← hL, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hg, ← map_sub,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← map_nsmul, hΦ.1.eq_iff]

end Algebra

section Measure

theorem covol_map {G G' : Type} [Mul G] [Mul G'] [MeasurableSpace G] [MeasurableSpace G'] (T : G' ≃ᵐ G)
    (hT : ∀ a b, T (a * b) = T a * T b) (Γ : Set G) (Γ' : Set G') (hΓ : ∀ g, g ∈ Γ' ↔ T g ∈ Γ)
    (μ' : Measure G') : covol Γ (μ'.map T) Set.univ = covol Γ' μ' Set.univ := by
  unfold covol
  apply le_antisymm
  · refine le_iInf fun D => le_iInf fun hD => le_iInf fun hc => ?_
    refine iInf_le_of_le (T.symm ⁻¹' D) (iInf_le_of_le (T.symm.measurable hD) (iInf_le_of_le ?_ ?_))
    · intro x _
      obtain ⟨γ, hγ, h⟩ := hc (T.symm x) trivial
      refine ⟨T γ, (hΓ γ).1 hγ, ?_⟩
      rw [← T.apply_symm_apply x, ← hT, Set.mem_preimage, T.symm_apply_apply]
      exact h
    · rw [T.map_apply, ← Set.preimage_comp]
      simp
  · refine le_iInf fun D => le_iInf fun hD => le_iInf fun hc => ?_
    refine iInf_le_of_le (T ⁻¹' D) (iInf_le_of_le (T.measurable hD) (iInf_le_of_le ?_ ?_))
    · intro x _
      obtain ⟨γ, hγ, h⟩ := hc (T x) trivial
      refine ⟨T.symm γ, (hΓ _).2 (by rwa [T.apply_symm_apply]), ?_⟩
      rw [Set.mem_preimage, hT, T.apply_symm_apply]
      exact h
    · rw [T.map_apply]

theorem covol_smul {G : Type} [Mul G] [MeasurableSpace G] (Γ : Set G) (μ : Measure G) (A : Set G)
    (a : ENNReal) (h0 : a ≠ 0) (ht : a ≠ ⊤) : covol Γ (a • μ) A = a * covol Γ μ A := by
  unfold covol
  simp only [ENNReal.mul_iInf_of_ne h0 ht, Measure.smul_apply, smul_eq_mul]

theorem pi_smul {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.coe_finset_prod, ← Finset.prod_mul_distrib]
  simp only [Measure.coe_nnreal_smul_apply]

theorem map_pi_smul {ι ι' : Type} [Fintype ι] [Fintype ι'] {α : ι → Type} {α' : ι' → Type}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (α' i)] (μ : ∀ i, Measure (α i))
    (μ' : ∀ i, Measure (α' i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)] (c : ι → ℝ≥0) (c' : ι' → ℝ≥0)
    (τ : ι ≃ ι') (T : ∀ i, α' (τ i) ≃ᵐ α i) (hT : ∀ i, (c' (τ i) • μ' (τ i)).map (T i) = c i • μ i) :
    ∃ Φ : (∀ i, α' i) ≃ᵐ (∀ i, α i), (∀ g i, Φ g i = T i (g (τ i))) ∧
      ((∏ i, c' i) • Measure.pi μ').map Φ = (∏ i, c i) • Measure.pi μ := by
  refine ⟨(MeasurableEquiv.piCongrLeft α' τ).symm.trans (MeasurableEquiv.piCongrRight T), fun g i => rfl, ?_⟩
  rw [← pi_smul, ← pi_smul]
  have h1 := (measurePreserving_piCongrLeft (fun i => c' i • μ' i) τ).symm
  have h2 := measurePreserving_pi (fun i => c' (τ i) • μ' (τ i)) (fun i => c i • μ i)
    (f := fun i => T i) (fun i => ⟨(T i).measurable, hT i⟩)
  exact (h2.comp h1).map_eq

theorem pos_of_isGauge {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  by_contra hc
  rw [not_lt] at hc
  have h1 := le_of_tendsto h (b := 0) (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _))
  exact absurd h1 (not_le.2 (ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne))

end Measure

section Real

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * _ * _ = _ ↔ Formalism.REAL.inUJ ε _
  rw [Formalism.UG.P.cT_conj_eq]
  rfl

theorem exists_perm {n : ℕ} {ε ε' : Fin n → Bool} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B)
    (h : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') : ∃ π : Fin n ≃ Fin n, ∀ a, ε (π a) = ε' a := by
  have h1 := GlobalTheory.AutInhab.hasSignature_of_frame hB h
  have h2 := GlobalTheory.AutInhab.hasSignature_of_frame (ε := ε) (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  obtain ⟨hp, hq⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 h2
  have hc : ∀ b : Bool, Fintype.card {a // ε' a = b} = Fintype.card {a // ε a = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases b
    · exact hq
    · exact hp
  exact ⟨Equiv.ofFiberEquiv fun b => Fintype.equivOfCardEq (hc b), fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_real_equiv {n m : ℕ} (hn : m = n) (ε : Fin n → Bool) (ε' : Fin m → Bool) (κ : ℂ ≃+* ℂ)
    (hκ : (∀ z, κ z = z) ∨ ∀ z, κ z = starRingEnd ℂ z)
    (B : Matrix (Fin n) (Fin m) ℂ) (B' : Matrix (Fin m) (Fin n) ℂ) (h1 : B * B' = 1) (h2 : B' * B = 1)
    (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ T : Formalism.REAL.UJ ε' ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (T g) = B * (uMat g).map κ * B') ∧
      ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' →
        (ENNReal.ofReal c' • Formalism.REAL.muG ε').map T = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  subst hn
  have k1 : ∀ z, κ (starRingEnd ℂ z) = starRingEnd ℂ (κ z) := by
    rcases hκ with h | h <;> simp [h]
  have k2 : ∀ z, κ (κ z) = z := by
    rcases hκ with h | h <;> simp [h]
  have k3 : ∀ z, ‖κ z‖ = ‖z‖ := by
    rcases hκ with h | h <;> simp [h]
  have k4 : Continuous κ := by
    rcases hκ with h | h
    · exact (funext h : (κ : ℂ → ℂ) = id) ▸ continuous_id
    · exact (funext h : (κ : ℂ → ℂ) = starRingEnd ℂ) ▸ Complex.continuous_conj
  have k5 : (Formalism.REAL.Jm ε').map κ = Formalism.REAL.Jm ε' := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  obtain ⟨T₀, hT₀⟩ := exists_unitary_equiv κ (starRingEnd ℂ) (starRingEnd ℂ) k1 (Formalism.REAL.Jm ε')
    (Formalism.REAL.Jm ε) B B' h1 h2 (by rw [Formalism.UG.P.cT_conj_eq, hB, k5])
  let T₁ : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε :=
    ((MulEquiv.subgroupCongr (realUJ_eq ε').symm).trans T₀).trans (MulEquiv.subgroupCongr (realUJ_eq ε))
  have hT₁ : ∀ g, uMat (T₁ g) = B * (uMat g).map κ * B' := fun g =>
    hT₀ (MulEquiv.subgroupCongr (realUJ_eq ε').symm g)
  have hT₂ : ∀ g, uMat (T₁.symm g) = (B' * uMat g * B).map κ := by
    intro g
    have := hT₁ (T₁.symm g)
    rw [T₁.apply_symm_apply] at this
    have e : B' * uMat g * B = (uMat (T₁.symm g)).map κ := by
      rw [this]
      calc _ = (B' * B) * (uMat (T₁.symm g)).map κ * (B' * B) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    rw [e]
    ext i j
    exact (k2 _).symm
  have hE := (Formalism.REAL.isClosedEmbeddingMatrix m ε).1
  have hE' := (Formalism.REAL.isClosedEmbeddingMatrix m ε').1
  have c1 : Continuous T₁ := by
    refine hE.isInducing.continuous_iff.2 ?_
    have : (fun g : Formalism.REAL.UJ ε => uMat g) ∘ T₁ = fun g => B * (uMat g).map κ * B' := funext hT₁
    rw [this]
    exact (continuous_const.matrix_mul (hE'.continuous.matrix_map k4)).matrix_mul continuous_const
  have c2 : Continuous T₁.symm := by
    refine hE'.isInducing.continuous_iff.2 ?_
    have : (fun g : Formalism.REAL.UJ ε' => uMat g) ∘ T₁.symm = fun g => (B' * uMat g * B).map κ := funext hT₂
    rw [this]
    exact ((continuous_const.matrix_mul hE.continuous).matrix_mul continuous_const).matrix_map k4
  let T : Formalism.REAL.UJ ε' ≃ₜ* Formalism.REAL.UJ ε := { T₁ with continuous_toFun := c1, continuous_invFun := c2 }
  have hT : ∀ g, uMat (T g) = B * (uMat g).map κ * B' := hT₁
  refine ⟨T, hT, fun c c' hc hc' => ?_⟩
  obtain ⟨π, hπ⟩ := exists_perm (IsUnit.of_mul_eq_one B' h1) hB
  let S : Matrix (Fin m) (Fin m) ℂ := (1 : Matrix (Fin m) (Fin m) ℂ).submatrix (Equiv.refl _) π
  have hS1 : ∀ M : Matrix (Fin m) (Fin m) ℂ, M * S = M.submatrix id π := fun M =>
    Matrix.mul_submatrix_one _ _ M
  have hS2 : ∀ M : Matrix (Fin m) (Fin m) ℂ, S * M = M.submatrix π.symm id := fun M =>
    Matrix.one_submatrix_mul _ _ M
  have hS3 : ∀ M : Matrix (Fin m) (Fin m) ℂ, Sᴴ * M = M.submatrix π id := by
    intro M
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    exact Matrix.one_submatrix_mul _ _ M
  have hSJ : Sᴴ * Formalism.REAL.Jm ε * S = Formalism.REAL.Jm ε' := by
    rw [hS3, hS1]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, hπ]
  have hSS : Sᴴ * S = 1 := by
    rw [hS1, Matrix.conjTranspose_submatrix]
    ext i j
    simp [Matrix.one_apply]
  have hSB : (S * B') * (B * Sᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h2, Matrix.one_mul, mul_eq_one_comm, hSS]
  have hJ' : B'ᴴ * Formalism.REAL.Jm ε' * B' = Formalism.REAL.Jm ε := by
    rw [← hB]
    calc _ = (B * B')ᴴ * Formalism.REAL.Jm ε * (B * B') := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  let w : Formalism.REAL.UJ ε := ⟨⟨S * B', B * Sᴴ, hSB, mul_eq_one_comm.1 hSB⟩, by
    change (S * B')ᴴ * Formalism.REAL.Jm ε * (S * B') = Formalism.REAL.Jm ε
    calc _ = B'ᴴ * (Sᴴ * Formalism.REAL.Jm ε * S) * B' := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hSJ, hJ']⟩
  refine GlobalTheory.FlagMeas.gauge_map_of_iso m m ε' ε rfl T (T.symm w) (fun g => ?_) c' c hc' hc
  have e : uMat (T (T.symm w * g * (T.symm w)⁻¹)) = ((uMat g).map κ).submatrix π.symm π.symm := by
    rw [map_mul, map_mul, map_inv, T.apply_symm_apply]
    change S * B' * uMat (T g) * (B * Sᴴ) = _
    rw [hT]
    calc _ = S * (B' * B) * (uMat g).map κ * (B' * B) * Sᴴ := by simp only [Matrix.mul_assoc]
      _ = S * (uMat g).map κ * Sᴴ := by rw [h2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
        rw [hS2, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, Matrix.mul_submatrix_one]
        rfl
  rw [e]
  unfold Formalism.REAL.hs
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← k3 ((uMat g - 1) i j)]
  simp [Matrix.one_apply, apply_ite κ]

end Real

section Adele

open IsDedekindDomain Formalism.UG

theorem exists_adele_equiv {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (e : E' ≃+* E) :
    ∃ ρ : E' ⊗[F'] Af F' ≃+* E ⊗[F] Af F, (∀ x, ρ (inclE (F := F') (Af F') x) = inclE (F := F) (Af F) (e x)) ∧
      ∀ y, y ∈ IntAf F' E' ↔ ρ y ∈ IntAf F E := by
  obtain ⟨a, a1, a2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E
  obtain ⟨b, b1, b2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F' E'
  letI : Algebra E' E := e.toRingHom.toAlgebra
  obtain ⟨c, c1, c2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv E' E
  let eA : E' ≃ₐ[E'] E := { e with commutes' := fun _ => rfl }
  let d : Af E' ≃+* E ⊗[E'] Af E' :=
    ((Algebra.TensorProduct.lid E' (Af E')).symm.trans
      (Algebra.TensorProduct.congr eA AlgEquiv.refl)).toRingEquiv
  have d0 : ∀ y, d y = 1 ⊗ₜ[E'] y := fun y => by simp [d]
  refine ⟨((b.trans d).trans c).trans a.symm, fun x => ?_, fun y => ?_⟩
  · change a.symm (c (d (b (x ⊗ₜ[F'] 1)))) = e x ⊗ₜ[F] 1
    rw [b1, d0, RingEquiv.symm_apply_eq, a1, ← c1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
    rfl
  · change _ ↔ a.symm (c (d (b y))) ∈ Formalism.L2.DIV.RInt F E
    rw [a2, a.apply_symm_apply, ← c2]
    refine (b2 y).trans ?_
    change b y ∈ intAd E' ↔ _
    constructor
    · intro h
      rw [d0]
      exact Subring.subset_closure (Or.inr ⟨⟨_, h⟩, rfl⟩)
    · intro h
      have : ∀ z ∈ Formalism.L2.DIV.RInt E' E, d.symm z ∈ intAd E' := by
        intro z hz
        refine (Subring.closure_le (t := (intAd E').comap d.symm.toRingHom)).2 ?_ hz
        rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨x, rfl⟩)
        · have := GlobalTheory.AdeleBaseChange.algebraMap_int_mem (RingOfIntegers.mapRingEquiv e.symm x)
          change d.symm _ ∈ intAd E'
          convert this using 1
          rw [RingEquiv.symm_apply_eq, d0, Algebra.algebraMap_eq_smul_one (A := Af E'), ← TensorProduct.smul_tmul,
            ← Algebra.algebraMap_eq_smul_one]
          exact congrArg (fun t : E => t ⊗ₜ[E'] (1 : Af E')) (e.apply_symm_apply _).symm
        · change d.symm (1 ⊗ₜ[E'] x.1) ∈ intAd E'
          rw [← d0, d.symm_apply_apply]
          exact x.2
      simpa using this _ h

theorem adele_hom_ext {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (f g : E' ⊗[F'] Af F' →+* E ⊗[F] Af F) (hf : ∀ y ∈ IntAf F' E', f y ∈ IntAf F E)
    (hg : ∀ y ∈ IntAf F' E', g y ∈ IntAf F E)
    (h : ∀ x, f (inclE (F := F') (Af F') x) = g (inclE (F := F') (Af F') x)) (y : E' ⊗[F'] Af F') : f y = g y := by
  rw [← sub_eq_zero]
  refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible _ fun N hN => ?_
  obtain ⟨x, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := F') (E := E') ((N : E')⁻¹ ⊗ₜ[F'] 1 * y)
  have e2 : y = N • (inclE (F := F') (Af F') x + r) := by
    change y = N • (x ⊗ₜ[F'] 1 + r)
    rw [← e, ← smul_mul_assoc, TensorProduct.smul_tmul', nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), ← Algebra.TensorProduct.one_def, one_mul]
  refine ⟨f r - g r, sub_mem (hf r hr) (hg r hr), ?_⟩
  rw [e2, map_nsmul, map_nsmul, map_add, map_add, h, ← smul_sub, add_sub_add_left_eq_sub]

end Adele

section Finite

open Formalism.UG

theorem mem_of_mem_span {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} {S : Subring R} {S' : Subring R'}
    (X : Set (Fin m → R')) (L : Submodule S (Fin n → R)) (Ψ : (Fin m → R') →+ (Fin n → R)) (ρ : R' → R)
    (hρ : ∀ s ∈ S', ρ s ∈ S) (hΨ : ∀ r w, Ψ (r • w) = ρ r • Ψ w) (hX : ∀ x ∈ X, Ψ x ∈ L) :
    ∀ w ∈ Submodule.span S' X, Ψ w ∈ L := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [Subring.smul_def, hΨ]
    exact L.smul_mem ⟨_, hρ _ c.2⟩ ha

theorem exists_inv {E : Type} [Field E] [StarRing E] {n m : ℕ} (h : m = n) {J : Matrix (Fin n) (Fin n) E}
    {J' : Matrix (Fin m) (Fin m) E} {A : Matrix (Fin n) (Fin m) E} (hA : Aᴴ * J * A = J') (hJ : J'.det ≠ 0) :
    ∃ A' : Matrix (Fin m) (Fin n) E, A * A' = 1 ∧ A' * A = 1 := by
  subst h
  have : IsUnit A.det := by
    refine IsUnit.mk0 _ fun h0 => hJ ?_
    rw [← hA, Matrix.det_mul, h0, mul_zero]
  exact ⟨A⁻¹, Matrix.mul_nonsing_inv _ this, Matrix.nonsing_inv_mul _ this⟩

theorem exists_fin_equiv (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (A' : Matrix (Fin I'.n) (Fin I.n) I.E) (xf : I.Gf) (he : ∀ y, e (star y) = star (e y))
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hA : Aᴴ * I.J * A = I'.J.map e)
    (hL : ∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)) :
    ∃ T : I'.Gf ≃ₜ* I.Gf, (∀ g, g ∈ I'.Kset ↔ xf⁻¹ * T g * xf ∈ I.Kset) ∧
      ∀ (g : I'.Gf) (γ : Matrix (Fin I'.n) (Fin I'.n) I'.E),
        I'.fmat g = γ.map (inclE (F := I'.F) (Af I'.F)) ↔
          I.fmat (T g) = (A * γ.map e * A').map (inclE (F := I.F) (Af I.F)) := by
  obtain ⟨ρ, r1, r2⟩ := exists_adele_equiv (F := I.F) (F' := I'.F) e
  set ι := inclE (F := I.F) (E := I.E) (Af I.F) with hι
  set ι' := inclE (F := I'.F) (E := I'.E) (Af I'.F) with hι'
  have s1 : ∀ x, sigR I.cm.sig (Af I.F) (ι x) = ι (star x) := fun x => rfl
  have s2 : ∀ x, sigR I'.cm.sig (Af I'.F) (ι' x) = ι' (star x) := fun x => rfl
  have r3 : ∀ y, ρ (sigR I'.cm.sig (Af I'.F) y) = sigR I.cm.sig (Af I.F) (ρ y) :=
    adele_hom_ext (ρ.toRingHom.comp (sigR I'.cm.sig (Af I'.F))) ((sigR I.cm.sig (Af I.F)).comp ρ.toRingHom)
      (fun y hy => (r2 _).1 (Formalism.UG.P.csScale_sigR_mem _ hy))
      (fun y hy => Formalism.UG.P.csScale_sigR_mem _ ((r2 _).1 hy))
      (fun x => by
        change ρ (sigR _ _ (ι' x)) = sigR _ _ (ρ (ι' x))
        rw [s2, r1, r1, s1, he])
  have k1 : A.map ι * A'.map ι = 1 := by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have k2 : A'.map ι * A.map ι = 1 := by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  have k3 : ∀ γ : Matrix (Fin I'.n) (Fin I'.n) I'.E, (γ.map ι').map ρ = (γ.map e).map ι := fun γ => by
    ext i j; exact r1 _
  obtain ⟨T₀, hT₀⟩ := exists_unitary_equiv ρ _ _ r3 (I'.J.map ι') (I.J.map ι) (A.map ι) (A'.map ι) k1 k2 (by
    rw [k3, ← hA, Matrix.map_mul, Matrix.map_mul]
    rfl)
  let T₁ : I'.Gf ≃* I.Gf := T₀
  have hT₁ : ∀ g, I.fmat (T₁ g) = A.map ι * (I'.fmat g).map ρ * A'.map ι := hT₀
  have hLf : I.Lf = latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf latS
    rw [Set.image_eq_range]
    rfl
  have hR : ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, I.fmat xf⁻¹ *ᵥ z ∈ I.Lf ↔
      z ∈ Submodule.span (IntAf I.F I.E)
        ((fun x i => ι (x i)) '' (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro z
    rw [GlobalTheory.PointEquivariance.lamX_eq, hLf]
    exact (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L
      (Module.Finite.iff_fg.2 I.L_fg) I.L_span _ z).symm
  let Ψ : (Fin I'.n → I'.E ⊗[I'.F] Af I'.F) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    { toFun := fun w => A.map ι *ᵥ fun i => ρ (w i)
      map_zero' := by
        have : (fun i => ρ ((0 : Fin I'.n → _) i)) = 0 := by funext i; simp
        rw [this, Matrix.mulVec_zero]
      map_add' := fun a b => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext i; simp }
  let Ψ' : (Fin I.n → I.E ⊗[I.F] Af I.F) →+ (Fin I'.n → I'.E ⊗[I'.F] Af I'.F) :=
    { toFun := fun z i => ρ.symm ((A'.map ι *ᵥ z) i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp [Matrix.mulVec_add] }
  have p1 : ∀ w, Ψ' (Ψ w) = w := fun w => by
    funext i
    change ρ.symm ((A'.map ι *ᵥ (A.map ι *ᵥ fun i => ρ (w i))) i) = w i
    rw [Matrix.mulVec_mulVec, k2, Matrix.one_mulVec, ρ.symm_apply_apply]
  have p2 : ∀ z, Ψ (Ψ' z) = z := fun z => by
    change (A.map ι *ᵥ fun i => ρ (ρ.symm ((A'.map ι *ᵥ z) i))) = z
    simp only [ρ.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, k1, Matrix.one_mulVec]
  have p3 : ∀ y : Fin I'.n → I'.E, Ψ (fun i => ι' (y i)) = fun i => ι ((A *ᵥ fun i => e (y i)) i) := by
    intro y
    funext i
    rw [RingHom.map_mulVec]
    change (A.map ι *ᵥ fun i => ρ (ι' (y i))) i = _
    simp only [r1]
    rfl
  have p4 : ∀ r w, Ψ (r • w) = ρ r • Ψ w := fun r w => by
    change (A.map ι *ᵥ fun i => ρ (r * w i)) = ρ r • (A.map ι *ᵥ fun i => ρ (w i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i; simp
  have p5 : ∀ r z, Ψ' (r • z) = ρ.symm r • Ψ' z := fun r z => by
    rw [← p1 (ρ.symm r • Ψ' z), p4, p2, ρ.apply_symm_apply]
  have hX : I.fmat xf * I.fmat xf⁻¹ = 1 := Units.mul_inv _
  have hXi : I.fmat xf⁻¹ * I.fmat xf = 1 := Units.inv_mul _
  let Φ := (Matrix.mulVecLin (I.fmat xf⁻¹)).toAddMonoidHom.comp Ψ
  have hΦ : ∀ w, Φ w = I.fmat xf⁻¹ *ᵥ Ψ w := fun w => rfl
  have hb : Function.Bijective Φ := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun z => Ψ' (I.fmat xf *ᵥ z), fun w => ?_, fun z => ?_⟩
    · simp only [hΦ]
      rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec, p1]
    · simp only [hΦ]
      rw [p2, Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec]
  have hmem : ∀ w, w ∈ I'.Lf ↔ Φ w ∈ I.Lf := by
    intro w
    rw [hΦ, hR]
    constructor
    · refine mem_of_mem_span _ _ Ψ ρ (fun s hs => (r2 s).1 hs) p4 ?_ w
      rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨_, (hL y).1 y.2, (p3 y).symm⟩
    · intro h
      rw [← p1 w]
      refine mem_of_mem_span _ _ Ψ' ρ.symm (fun s hs => (r2 _).2 (by rwa [ρ.apply_symm_apply])) p5 ?_ _ h
      rintro _ ⟨y, hy, rfl⟩
      have e1 : (A *ᵥ fun i => e (e.symm ((A' *ᵥ y) i))) = y := by
        simp only [e.apply_symm_apply]
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      have e2 := p3 fun i => e.symm ((A' *ᵥ y) i)
      rw [e1] at e2
      beta_reduce
      rw [← e2, p1]
      exact Submodule.subset_span ⟨⟨_, (hL _).2 (by rwa [e1])⟩, rfl⟩
  have key := fun g : I'.Gf => stab_and_cong I.Lf I'.Lf Φ hb hmem (I'.fmat g)
    (I.fmat xf⁻¹ * I.fmat (T₁ g) * I.fmat xf) (fun w => by
      rw [hΦ, hΦ, Matrix.mulVec_mulVec, Matrix.mul_assoc, hX, Matrix.mul_one, ← Matrix.mulVec_mulVec, hT₁]
      congr 1
      change _ *ᵥ (A.map ι *ᵥ fun i => ρ (w i)) = A.map ι *ᵥ fun i => ρ ((I'.fmat g *ᵥ w) i)
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, k2, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      congr 1
      funext i
      exact (RingHom.map_mulVec ρ.toRingHom _ _ i).symm)
  have hK : ∀ g, g ∈ I'.Kset ↔ xf⁻¹ * T₁ g * xf ∈ I.Kset := fun g => (key g).1
  have hE := GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg I I' T₁.toMonoidHom xf
    fun N g => and_congr (hK g) ((key g).2 N)
  have c2 : Continuous T₁.symm := hE.isInducing.continuous_iff.2 (by
    have : (T₁.toMonoidHom : I'.Gf → I.Gf) ∘ T₁.symm = id := funext T₁.apply_symm_apply
    rw [this]
    exact continuous_id)
  refine ⟨{ T₁ with continuous_toFun := hE.continuous, continuous_invFun := c2 }, hK, fun g γ => ?_⟩
  change _ ↔ I.fmat (T₁ g) = _
  rw [hT₁, Matrix.map_mul, Matrix.map_mul, ← k3]
  exact (conjMat ρ (A.map ι) (A'.map ι) k1 k2).injective.eq_iff.symm

end Finite

section Places

theorem exists_kappa (I : AutInst) (ψ : I.E →+* ℂ) :
    ∃ κ : ℂ ≃+* ℂ, ((∀ z, κ z = z) ∨ ∀ z, κ z = starRingEnd ℂ z) ∧
      ∀ x, ψ x = κ (I.φ (InfinitePlace.mk (ψ.comp (algebraMap I.F I.E))) x) := by
  have h1 := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk ψ)
  rw [InfinitePlace.comap_mk] at h1
  rcases InfinitePlace.embedding_mk_eq ψ with h | h <;> rw [h] at h1 <;> rcases h1 with h1 | h1
  · exact ⟨RingEquiv.refl ℂ, Or.inl fun _ => rfl, fun x => DFunLike.congr_fun h1 x⟩
  · exact ⟨starRingAut, Or.inr fun _ => rfl, fun x => DFunLike.congr_fun h1 x⟩
  · refine ⟨starRingAut, Or.inr fun _ => rfl, fun x => ?_⟩
    rw [← DFunLike.congr_fun h1 x]
    exact (star_star _).symm
  · exact ⟨RingEquiv.refl ℂ, Or.inl fun _ => rfl, fun x => star_injective (DFunLike.congr_fun h1 x)⟩

def placeMap (I I' : AutInst) (e : I'.E ≃+* I.E) (v : InfinitePlace I.F) : InfinitePlace I'.F :=
  InfinitePlace.mk (((I.φ v).comp e.toRingHom).comp (algebraMap I'.F I'.E))

theorem placeMap_placeMap (I I' : AutInst) (e : I'.E ≃+* I.E) (v : InfinitePlace I.F) :
    placeMap I' I e.symm (placeMap I I' e v) = v := by
  obtain ⟨κ, hκ, h⟩ := exists_kappa I' ((I.φ v).comp e.toRingHom)
  have h' : ∀ a : I.F, v.embedding a = κ (I'.φ (placeMap I I' e v) (e.symm (algebraMap I.F I.E a))) := by
    intro a
    rw [← I.φ_over]
    refine Eq.trans ?_ (h _)
    exact congrArg (I.φ v) (e.apply_symm_apply _).symm
  refine Eq.trans ?_ (InfinitePlace.mk_embedding v)
  rw [placeMap, InfinitePlace.mk_eq_iff]
  rcases hκ with hκ | hκ
  · exact Or.inl (RingHom.ext fun a => by rw [h', hκ]; rfl)
  · exact Or.inr (RingHom.ext fun a => by rw [h', hκ]; rfl)

def placeEquiv (I I' : AutInst) (e : I'.E ≃+* I.E) : InfinitePlace I.F ≃ InfinitePlace I'.F where
  toFun := placeMap I I' e
  invFun := placeMap I' I e.symm
  left_inv := placeMap_placeMap I I' e
  right_inv := placeMap_placeMap I' I e.symm

theorem exists_place_equiv (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (A' : Matrix (Fin I'.n) (Fin I.n) I.E) (hn : I'.n = I.n)
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hA : Aᴴ * I.J * A = I'.J.map e) (v : InfinitePlace I.F) :
    ∃ T : Formalism.REAL.UJ (I'.ε (placeEquiv I I' e v)) ≃ₜ* Formalism.REAL.UJ (I.ε v),
      (∀ g (γ : Matrix (Fin I'.n) (Fin I'.n) I'.E),
        uMat g = (I'.P (placeEquiv I I' e v))⁻¹ * γ.map (I'.φ (placeEquiv I I' e v)) *
            I'.P (placeEquiv I I' e v) ↔
          uMat (T g) = (I.P v)⁻¹ * (A * γ.map e * A').map (I.φ v) * I.P v) ∧
      ∀ c c' : ℝ, IsGauge (I.ε v) c → IsGauge (I'.ε (placeEquiv I I' e v)) c' →
        (ENNReal.ofReal c' • Formalism.REAL.muG (I'.ε (placeEquiv I I' e v))).map T =
          ENNReal.ofReal c • Formalism.REAL.muG (I.ε v) := by
  obtain ⟨κ, hκ, h⟩ := exists_kappa I' ((I.φ v).comp e.toRingHom)
  replace h : ∀ x, I.φ v (e x) = κ (I'.φ (placeEquiv I I' e v) x) := h
  generalize placeEquiv I I' e v = v' at h ⊢
  have m1 : ∀ γ : Matrix (Fin I'.n) (Fin I'.n) I'.E, (γ.map e).map (I.φ v) = (γ.map (I'.φ v')).map κ :=
    fun γ => by ext i j; exact h _
  have m2 : ∀ X Y : Matrix (Fin I'.n) (Fin I'.n) ℂ, (X * Y).map κ = X.map κ * Y.map κ :=
    fun X Y => Matrix.map_mul (f := κ.toRingHom)
  have m3 : (1 : Matrix (Fin I'.n) (Fin I'.n) ℂ).map κ = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have m4 : ((I'.P v').map κ)ᴴ = (I'.P v')ᴴ.map κ := by
    ext i j
    rcases hκ with h | h <;> simp [h]
  have m5 : (Formalism.REAL.Jm (I'.ε v')).map κ = Formalism.REAL.Jm (I'.ε v') := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have m6 : (A.map (I.φ v))ᴴ = Aᴴ.map (I.φ v) := by
    ext i j
    exact (I.cm.cmUnram.2.1 _ _).symm
  have a1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have a2 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have b1 : (I'.P v').map κ * (I'.P v')⁻¹.map κ = 1 := by
    rw [← m2, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I'.P_unit v')), m3]
  have b2 := mul_eq_one_comm.1 b1
  have k1 : A.map (I.φ v) * A'.map (I.φ v) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have k2 : A'.map (I.φ v) * A.map (I.φ v) = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  have q1 : (I.P v)⁻¹ * A.map (I.φ v) * (I'.P v').map κ * ((I'.P v')⁻¹.map κ * A'.map (I.φ v) * I.P v) = 1 := by
    calc _ = (I.P v)⁻¹ * (A.map (I.φ v) * ((I'.P v').map κ * (I'.P v')⁻¹.map κ) * A'.map (I.φ v)) * I.P v := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [b1, Matrix.mul_one, k1, Matrix.mul_one, a2]
  have q2 : (I'.P v')⁻¹.map κ * A'.map (I.φ v) * I.P v * ((I.P v)⁻¹ * A.map (I.φ v) * (I'.P v').map κ) = 1 := by
    calc _ = (I'.P v')⁻¹.map κ * (A'.map (I.φ v) * (I.P v * (I.P v)⁻¹) * A.map (I.φ v)) * (I'.P v').map κ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [a1, Matrix.mul_one, k2, Matrix.mul_one, b2]
  obtain ⟨T, hT, hm⟩ := exists_real_equiv hn (I.ε v) (I'.ε v') κ hκ _ _ q1 q2 (by
    rw [← I.P_spec v, ← m5, ← I'.P_spec v', m2, m2, ← m1, ← hA, Matrix.map_mul, Matrix.map_mul, ← m6, ← m4]
    calc _ = ((I'.P v').map κ)ᴴ * ((A.map (I.φ v))ᴴ * ((I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) *
            (I.P v * (I.P v)⁻¹)) * A.map (I.φ v)) * (I'.P v').map κ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨T, fun g γ => ?_, hm⟩
  rw [hT, ← (conjMat κ _ _ q1 q2).injective.eq_iff]
  refine Eq.congr_right ?_
  change (I.P v)⁻¹ * A.map (I.φ v) * (I'.P v').map κ *
    ((I'.P v')⁻¹ * γ.map (I'.φ v') * I'.P v').map κ * ((I'.P v')⁻¹.map κ * A'.map (I.φ v) * I.P v) = _
  rw [m2, m2, Matrix.map_mul, Matrix.map_mul, m1]
  calc _ = (I.P v)⁻¹ * (A.map (I.φ v) * ((I'.P v').map κ * (I'.P v')⁻¹.map κ) * (γ.map (I'.φ v')).map κ *
          ((I'.P v').map κ * (I'.P v')⁻¹.map κ) * A'.map (I.φ v)) * I.P v := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [b1, Matrix.mul_one, Matrix.mul_one]

end Places

theorem gaugeVol_transport : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), (∀ y, e (star y) = star (e y)) → I'.n = I.n → Aᴴ * I.J * A = I'.J.map e → (∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)) → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure], IsGaugeAll I c → IsGaugeAll I' c' → gaugeVol I c μf = gaugeVol I' c' μf' := by
  intro I I' e A xf he hn hA hL c μf _ _ c' μf' _ _ hc hc'
  obtain ⟨A', h1, h2⟩ := exists_inv hn hA (by
    have := (IsUnit.mk0 _ I'.J_det).map (e : I'.E →+* I.E)
    rw [RingHom.map_det] at this
    exact this.ne_zero)
  obtain ⟨Tf, hK, hf⟩ := exists_fin_equiv I I' e A A' xf he h1 h2 hA hL
  choose Tv hv hm using exists_place_equiv I I' e A A' hn h1 h2 hA
  obtain ⟨Tq, hq⟩ := exists_unitary_equiv e (starRingEnd I'.E) (starRingEnd I.E) he I'.J I.J A A' h1 h2 hA
  obtain ⟨Φ, hΦ, hΦm⟩ := map_pi_smul (fun v => Formalism.REAL.muG (I.ε v)) (fun v => Formalism.REAL.muG (I'.ε v))
    (fun v => (c v).toNNReal) (fun v => (c' v).toNNReal) (placeEquiv I I' e)
    (fun v => (Tv v).toHomeomorph.toMeasurableEquiv) (fun v => hm v _ _ (hc v) (hc' _))
  obtain ⟨-, hlc, hsc, hcK, hoK, -⟩ := GlobalTheory.CongTop.adelic_topology I
  let Ψ : I'.Gf ≃ᵐ I.Gf := Tf.toHomeomorph.toMeasurableEquiv
  have hΨ : ∀ g, Ψ g = Tf g := fun _ => rfl
  haveI : (μf'.map Ψ).IsHaarMeasure := Tf.isHaarMeasure_map μf'
  have ha := Measure.isMulLeftInvariant_eq_smul (μf'.map Ψ) μf
  have ha0 := Measure.haarScalarFactor_pos_of_isHaarMeasure (μf'.map Ψ) μf
  generalize Measure.haarScalarFactor (μf'.map Ψ) μf = a at ha ha0
  have hKm : μf' I'.Kset = a * μf I.Kset := by
    have e1 : I'.Kset = Ψ ⁻¹' ((fun x => xf⁻¹ * x) ⁻¹' ((fun x => x * xf) ⁻¹' I.Kset)) := Set.ext hK
    rw [e1, ← Ψ.map_apply, measure_preimage_mul, ha, Measure.coe_nnreal_smul_apply,
      ← Measure.map_apply (measurable_mul_const xf) hoK.measurableSet,
      (GlobalTheory.AdelicUnimod.adelic_unimodular I μf).2.2.2.1 xf]
  let T : I'.GA ≃ᵐ I.GA := Φ.prodCongr Ψ
  have hT : ∀ x, T x = (Φ x.1, Tf x.2) := fun _ => rfl
  have hmul : ∀ x y, T (x * y) = T x * T y := by
    intro x y
    refine Prod.ext (funext fun v => ?_) (map_mul Tf _ _)
    change Φ (x.1 * y.1) v = Φ x.1 v * Φ y.1 v
    rw [hΦ, hΦ, hΦ]
    exact map_mul (Tv v) _ _
  have hΓ : ∀ x, x ∈ I'.GFset ↔ T x ∈ I.GFset := by
    intro x
    have key : ∀ γ : Formalism.UG.UJ (starRingEnd I'.E) I'.J,
        ((∀ v, uMat (x.1 v) = (I'.P v)⁻¹ * γ.1.1.map (I'.φ v) * I'.P v) ∧
          I'.fmat x.2 = γ.1.1.map (Formalism.UG.inclE (F := I'.F) (Af I'.F))) ↔
        ((∀ v, uMat ((T x).1 v) = (I.P v)⁻¹ * (Tq γ).1.1.map (I.φ v) * I.P v) ∧
          I.fmat (T x).2 = (Tq γ).1.1.map (Formalism.UG.inclE (F := I.F) (Af I.F))) := by
      intro γ
      rw [hq, (placeEquiv I I' e).surjective.forall]
      refine and_congr (forall_congr' fun v => ?_) (hf _ _)
      rw [hv, show (T x).1 v = Tv v (x.1 (placeEquiv I I' e v)) from hΦ x.1 v]
    constructor
    · rintro ⟨γ, hγ, h⟩
      exact ⟨_, (Tq ⟨γ, hγ⟩).2, (key ⟨γ, hγ⟩).1 h⟩
    · rintro ⟨γ, hγ, h⟩
      refine ⟨_, (Tq.symm ⟨γ, hγ⟩).2, (key _).2 ?_⟩
      rw [Tq.apply_symm_apply]
      exact h
  have hC : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ), IsGaugeAll I c →
      ENNReal.ofReal (∏ v, c v) = ((∏ v, (c v).toNNReal : ℝ≥0) : ENNReal) ∧
        ((∏ v, (c v).toNNReal : ℝ≥0) : ENNReal) ≠ 0 := by
    intro I c hc
    have e1 : ENNReal.ofReal (∏ v, c v) = ((∏ v, (c v).toNNReal : ℝ≥0) : ENNReal) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun v _ => (pos_of_isGauge (hc v)).le, ENNReal.coe_finset_prod]
      rfl
    exact ⟨e1, e1 ▸ (ENNReal.ofReal_pos.2 (Finset.prod_pos fun v _ => pos_of_isGauge (hc v))).ne'⟩
  obtain ⟨e1, n1⟩ := hC I c hc
  obtain ⟨e2, n2⟩ := hC I' c' hc'
  have a0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.2 ha0.ne'
  unfold gaugeVol
  rw [e1, e2]
  generalize ∏ v, (c v).toNNReal = C at hΦm n1 ⊢
  generalize ∏ v, (c' v).toNNReal = C' at hΦm n2 ⊢
  have hμ : ((C' : ENNReal) • I'.muA μf').map T = ((a : ENNReal) * C) • I.muA μf := by
    unfold AutInst.muA
    rw [← Measure.prod_smul_left]
    refine (Measure.map_prod_map _ _ Φ.measurable Ψ.measurable).symm.trans ?_
    have : Measure.map Φ ((C' : ENNReal) • Measure.pi fun v => Formalism.REAL.muG (I'.ε v)) =
      (C : ENNReal) • Measure.pi fun v => Formalism.REAL.muG (I.ε v) := hΦm
    rw [this, ha, Measure.prod_smul_left, Measure.prod_smul_right, mul_comm, mul_smul]
    rfl
  rw [← covol_smul _ _ _ _ n2 ENNReal.coe_ne_top, ← covol_map T hmul I.GFset I'.GFset hΓ, hμ,
    covol_smul _ _ _ _ (mul_ne_zero a0 n1) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top), hKm,
    mul_assoc, ENNReal.mul_div_mul_left _ _ a0 ENNReal.coe_ne_top]

end GlobalTheory.GaugeTransport
