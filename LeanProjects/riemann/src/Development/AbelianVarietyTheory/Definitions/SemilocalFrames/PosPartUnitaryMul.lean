import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.StatementB
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec

variable {n : ℕ}

def muInt (lam : Fin n → ℝ) (a : Fin n) : ℤ := ⌊lam a + Formalism.QuantumDeterminants.rhoStd n a⌋

def sInt (lam : Fin n → ℝ) (i : Fin n) : ℤ :=
  muInt lam i - (if h : i.val + 1 < n then muInt lam ⟨i.val + 1, h⟩ else 0)

def Omega (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0}

def Phi (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i))

def IsLo (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, i < j → b i j = 0

def IsUp (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → b i j = 0

def KC (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {y | IsUnit y ∧ y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * y}

def IsTau (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) : Prop :=
  FiniteDimensional ℂ W ∧ Formalism.QuantumDeterminants.IsCRepOn (KC ε) τ ∧
    (∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε}) ∧
    (∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) ∧
    (∀ S : Submodule ℂ W, IsKStableOn ε τ S → S = ⊥ ∨ S = ⊤) ∧
    ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w ∧
    ∀ y ∈ KC ε, IsLoUni y → τ y w = w

def ps (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (z : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (Module.finrank ℂ W : ℂ) • ∫ k : Formalism.REAL.KG ε,
    Phi lam ((Formalism.REAL.toMK k)⁻¹ * z * Formalism.REAL.toMK k) •
      (innerSL ℂ (τ (Formalism.REAL.toMK k) w)).smulRight (τ (Formalism.REAL.toMK k) w) ∂(Formalism.REAL.muK ε)

def U1 (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ k ∈ Formalism.REAL.Kset ε, k⁻¹ * z * k ∈ Omega n}

def posPart (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Classical.epsilon fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g

def Psi (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (g : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (τ (g * (posPart g)⁻¹)).comp (ps ε lam τ w (posPart g))

def cycWord {m : ℕ} (a : Fin (m + 1) → Fin n) : List (Fin n × Fin n) :=
  List.ofFn fun i => (a i, a (finRotate (m + 1) i))

def gelf (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (m + 1) → Fin n, Formalism.REAL.Eword ε (cycWord a) f g

def Rhol (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => deriv (fun t : ℂ => F (z * NormedSpace.exp (t • Matrix.single a b (1 : ℂ)))) 0

def RholW (w : List (Fin n × Fin n)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  w.foldr (fun p G => Rhol p.1 p.2 G) F

def gelfH (m : ℕ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => ∑ a : Fin (m + 1) → Fin n, RholW (cycWord a) F z

def gelfVal (χ : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) a b

def IsZEigen (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∀ g ∈ UJset ε, gelf ε m f g = gelfVal χ (m + 1) * f g

def IsZFinite (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∃ (N : ℕ) (c : Fin N → ℂ), ∀ g ∈ UJset ε,
    (gelf ε m)^[N] f g = ∑ i, c i * (gelf ε m)^[i.val] f g

def IsBiKFin (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F : Formalism.REAL.UJ ε → ℂ |
    ∃ k₁ ∈ Formalism.REAL.Kset ε, ∃ k₂ ∈ Formalism.REAL.Kset ε, F = fun g => f (k₁ * umat g * k₂)})

def HasInfChar (ε : Fin n → Bool) (χ : Fin n → ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
    IsZEigen ε χ (fun g => ⟪w, σ g v⟫_ℂ)

def IsSqIntIrr (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ

def UEquiv (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ T : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ v, T (σ g v) = σ' g (T v)

def decHS (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * q)))

def stdRep (y : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y

theorem stdRep_apply (y : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    stdRep y v i = ∑ j, y i j * v j := rfl

theorem mem_Kset_allPos {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos n) := by
  refine ⟨hg, ?_⟩
  simp [Formalism.REAL.Jm, allPos]

theorem stdRep_irred (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hS : IsKStableOn (allPos n) stdRep S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff S).1 hne
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (by ext j; simpa using h j)
  have hD : Matrix.diagonal (fun a => if a = i then (-1 : ℂ) else 1) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h : a = i <;> simp [h]
  have h1 := S.smul_mem (2 * v i)⁻¹ (S.sub_mem hv (hS _ (mem_Kset_allPos hD) v hv))
  have e1 : (2 * v i)⁻¹ • (v - stdRep (Matrix.diagonal (fun a => if a = i then (-1 : ℂ) else 1)) v) =
      EuclideanSpace.single i (1 : ℂ) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [stdRep_apply, Matrix.diagonal_apply]
      field_simp
      ring
    · simp [stdRep_apply, Matrix.diagonal_apply, h]
  rw [e1] at h1
  have h2 : ∀ j, EuclideanSpace.single j (1 : ℂ) ∈ S := by
    intro j
    have hP : (Equiv.swap i j).permMatrix ℂ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul]
      simp
    have := hS _ (mem_Kset_allPos hP) _ h1
    convert this using 1
    ext a
    simp [stdRep_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_eq_iff, Pi.single_apply]
  rw [eq_top_iff]
  intro x _
  rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr x]
  exact S.sum_mem fun j _ => S.smul_mem _ (by simpa using h2 j)

theorem isTau_std (n : ℕ) :
    IsTau (allPos (n + 1)) (-Pi.single (Fin.last n) (1 : ℝ)) stdRep
      (EuclideanSpace.single (Fin.last n) (1 : ℂ)) := by
  refine ⟨inferInstance, ⟨?_, ?_⟩, ?_, ?_, stdRep_irred, by simp, ?_, ?_⟩
  · exact map_one (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ))
  · intro a _ b _
    exact map_mul (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)) a b
  · intro u v
    apply Differentiable.differentiableOn
    simp only [PiLp.inner_apply, stdRep_apply, Matrix.of_apply, RCLike.inner_apply]
    fun_prop
  · intro y _ u v
    have : stdRep yᴴ = ContinuousLinearMap.adjoint (stdRep y) :=
      map_star (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)) y
    rw [this, ContinuousLinearMap.adjoint_inner_right]
  · intro θ _
    ext i
    by_cases h : i = Fin.last n <;> simp [stdRep_apply, Matrix.diagonal_apply, Pi.single_apply, h]
  · intro y _ hy
    ext i
    by_cases h : i = Fin.last n
    · simp [stdRep_apply, Pi.single_apply, h, (hy _ _).2 rfl]
    · simp [stdRep_apply, Pi.single_apply, h, (hy i _).1 (Fin.lt_last_iff_ne_last.2 h)]

theorem IsZEigen.smooth {ε : Fin n → Bool} {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : IsZEigen ε χ f) : Formalism.REAL.SmoothOnG ε f := h.1

theorem IsZFinite.smooth {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : IsZFinite ε f) : Formalism.REAL.SmoothOnG ε f := h.1

theorem IsZEigen.isZFinite {ε : Fin n → Bool} {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : IsZEigen ε χ f) : IsZFinite ε f :=
  ⟨h.1, fun m => ⟨1, fun _ => gelfVal χ (m + 1), fun g hg => by simpa using h.2 m g hg⟩⟩

theorem gelfVal_succ (χ : Fin n → ℂ) (k : ℕ) :
    gelfVal χ (k + 1) = ∑ a, ((Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) *ᵥ
      (fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ))) a := by
  have h : Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) *ᵥ (fun _ => (1 : ℂ)) =
      fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ) := by
    funext a
    have e : ∀ b : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
        (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if b ∈ Finset.Ioi a then 1 else 0) := by
      intro b
      by_cases h1 : a = b
      · subst h1; simp
      · by_cases h2 : a < b <;> simp [h1, h2]
    have hc : (((Finset.Ioi a).card : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℕ) := by
      have := a.isLt
      rw [Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp only [Matrix.mulVec, dotProduct, Formalism.REAL.Amat, Matrix.of_apply, mul_one, e,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hc, Formalism.QuantumDeterminants.rhoStd]
    push_cast
    ring
  rw [← h, Matrix.mulVec_mulVec, ← pow_succ]
  simp [gelfVal, Matrix.mulVec, dotProduct]

theorem gelfVal_rho (k : ℕ) : gelfVal (fun a => (Formalism.QuantumDeterminants.rhoStd n a : ℂ)) (k + 1) = 0 := by
  rw [gelfVal_succ]
  simp [Matrix.mulVec, dotProduct]

theorem Eword_const (ε : Fin n → Bool) (c : ℂ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword ε (p :: w) (fun _ => c) = fun _ => 0 := by
  induction w generalizing p with
  | nil => funext g; simp [Formalism.REAL.Eword, Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]
  | cons q w ih =>
    funext g
    rw [Formalism.REAL.Eword]
    simp only [ih q]
    simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isZEigen_const (ε : Fin n → Bool) (c : ℂ) :
    IsZEigen ε (fun a => (Formalism.QuantumDeterminants.rhoStd n a : ℂ)) (fun _ => c) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => c, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
  intro m g _
  simp [gelf, cycWord, List.ofFn_succ, Eword_const, gelfVal_rho]

end Smooth

theorem isSqIntIrr_std (n : ℕ) : IsSqIntIrr (allPos (n + 1)) stdRep := by
  have hU : ∀ g, g ∈ UJset (allPos (n + 1)) ↔ g ∈ Formalism.REAL.Kset (allPos (n + 1)) := by
    intro g
    simp [UJset, Formalism.REAL.inUJ, Formalism.REAL.Kset, Formalism.REAL.Jm, allPos, Matrix.mem_unitaryGroup_iff',
      Matrix.star_eq_conjTranspose]
  have hc : ∀ v, Continuous fun g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => stdRep g v := by
    intro v
    refine (PiLp.continuous_toLp 2 _).comp (f := fun g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
      fun i => ∑ j, g i j * v j) ?_
    fun_prop
  refine ⟨inferInstance, inferInstance, ⟨⟨(isTau_std n).2.1.1, fun a _ b _ => ?_⟩, ?_,
    fun v => (hc v).continuousOn⟩, ?_, ?_⟩
  · exact map_mul (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)) a b
  · intro g hg v
    have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem ((hU g).1 hg).1
    have h2 : stdRep gᴴ = ContinuousLinearMap.adjoint (stdRep g) :=
      map_star (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)) g
    apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).2
    rw [← h2]
    have := map_mul (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)) gᴴ g
    rw [h1, map_one] at this
    exact this.symm
  · intro S _ hS
    exact stdRep_irred S fun g hg => hS g ((hU g).2 hg)
  · intro v w
    have hemb := Formalism.REAL.isClosedEmbeddingMatrix (n + 1) (allPos (n + 1))
    haveI : CompactSpace (Formalism.REAL.UJ (allPos (n + 1))) := by
      rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
      convert (Formalism.REAL.maximal_compact_facts (n + 1) (allPos (n + 1))).2.1 using 1
      exact Set.ext hU
    have hf : Continuous (coefOn (ε := allPos (n + 1)) stdRep v w) :=
      continuous_const.inner ((hc v).comp hemb.1.continuous)
    exact hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

open scoped MatrixOrder in

theorem posPart_posDef_sq {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) :
    (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g := by
  apply Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g)
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ gᴴ * g := (Matrix.posSemidef_conjTranspose_mul_self g).nonneg
  have hs : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ h0
  refine ⟨CFC.sqrt (gᴴ * g), ?_, hs⟩
  rw [(Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (gᴴ * g))).posDef_iff_isUnit]
  have hu : IsUnit (gᴴ * g) := (by simpa [Matrix.star_eq_conjTranspose] using hg.star : IsUnit gᴴ).mul hg
  rw [← hs] at hu
  exact isUnit_of_mul_isUnit_left hu

open scoped MatrixOrder in

theorem posPart_eq_of_sq {g p : Matrix (Fin n) (Fin n) ℂ} (hp : p.PosDef) (h : p * p = gᴴ * g) :
    posPart g = p := by
  obtain ⟨h1, h2⟩ : (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g :=
    Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g) ⟨p, hp, h⟩
  rw [← CFC.sqrt_unique h2 h1.posSemidef.nonneg, ← CFC.sqrt_unique h hp.posSemidef.nonneg]

theorem posPart_unitary_mul {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hp : p.PosDef) : posPart (k * p) = p := by
  apply posPart_eq_of_sq hp
  have h : kᴴ * k = 1 := Unitary.star_mul_self_of_mem hk
  rw [Matrix.conjTranspose_mul, hp.1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, h, Matrix.one_mul]

theorem Psi_unitary_mul (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W)
    {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hp : p.PosDef) :
    Psi ε lam τ w (k * p) = (τ k).comp (ps ε lam τ w p) := by
  unfold Psi
  rw [posPart_unitary_mul hk hp,
    Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det p).1 hp.isUnit)]

theorem Phi_at_one (lam : Fin n → ℝ) : Phi lam 1 = 1 := by
  unfold Phi leadMinor
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _)]
  simp

example (lam : Fin 2 → ℝ) (z : Matrix (Fin 2) (Fin 2) ℂ) :
    Phi lam z = z 0 0 ^ (-(muInt lam 0 - muInt lam 1)) * z.det ^ (-(muInt lam 1)) := by
  simp [Phi, Fin.prod_univ_two, leadMinor, sInt]

end GlobalTheory.Dec
