import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.StdCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem conj_unit_iff {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = 1 ↔ U * Uᴴ = 1 := by
  have e : U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = (U * Uᴴ).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
  constructor
  · intro h
    rw [e] at h
    have h2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = (1 : Matrix ι ι ℂ).map (starRingEnd ℂ) := by rw [h]
    have e2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = U * Uᴴ := by
      ext i j
      simp only [Matrix.map_apply, Complex.conj_conj]
    rw [e2, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · intro h
    rw [e, h]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inFrame_eq (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    inFrame b x = (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
  have hinv : (bA (F := F) b)⁻¹ = bA (F := F) b⁻¹ :=
    (map_inv (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))) b).symm
  rw [frameEquiv_val, hinv]
  rfl

theorem mem_O_iff (hD : Dict) (χ : Chr F E) (y : AE F E) :
    y ∈ (adCM σ χ).O ↔ finOne F • y ∈ intHat F E :=
  (hD F E).2.2.2.1 y

theorem unit_iff (hI : DictInf) (hcm : IsCMExt F E σ) (χ : Chr F E) (B : Base F E)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (∀ w, M.map (piInf (B.emb w)) * (M.map (piInf (B.emb w)))ᴴ = 1) ↔
      ∀ w, M.map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have key : ∀ (τ : AE F E →+* ℂ) (w' : InfinitePlace E),
      ((∀ z, τ z = (adStd E).φ w' (eqv F E z)) ∨ ∀ z, τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) →
      (M.map τ * (M.map τ)ᴴ = 1 ↔ M.map ((adCM σ χ).φ w') ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) := by
    intro τ w' h
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rcases h with h | h
    · have e : M.map τ = M.map ((adCM σ χ).φ w') := by
        ext i j
        exact h _
      rw [e]
    · have e : M.map τ = (M.map ((adCM σ χ).φ w')).map (starRingEnd ℂ) := by
        ext i j
        exact h _
      rw [e]
      exact conj_unit_iff _
  obtain ⟨h1, h2⟩ := (hI F E σ hcm).2 B.emb
  constructor
  · intro h w'
    obtain ⟨w, hw⟩ := h2 w'
    exact (key _ w' hw).1 (h w)
  · intro h w
    obtain ⟨w', hw⟩ := h1 w
    exact (key _ w' hw).2 (h w')

theorem mem_isStdK_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  intro F E _ _ _ _ _ σ n Y hD hI hcm χ ε b hb B K hK x
  have hinv : inFrame b x⁻¹ = ((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [inFrame_eq χ ε b hb x⁻¹, map_inv]
    rfl
  have hx := inFrame_eq χ ε b hb x
  rw [hK x]
  show _ ↔ (frameEquiv χ ε b hb x).1 ∈ (adCM σ χ).kGL (Fin n ⊕ Fin n)
  show _ ↔ (∀ r c, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) r c ∈ (adCM σ χ).O ∧
      (((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (AE F E))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) r c ∈ (adCM σ χ).O) ∧
      ∀ w, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
  rw [← hinv, ← hx, ← unit_iff hI hcm χ B, and_comm]
  refine and_congr ?_ Iff.rfl
  simp only [mem_O_iff (σ := σ) hD χ]
  constructor
  · intro h r c
    exact ⟨h x (by simp) r c, h x⁻¹ (by simp) r c⟩
  · intro h k' hk' r c
    rcases hk' with rfl | hk'
    · exact (h r c).1
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact (h r c).2

end GlobalTheory.CompanionTheory.SiegelFrame.StdCompact
