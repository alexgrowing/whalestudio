import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

section Gen

variable {H : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_scale (ν : Measure H) [ν.IsAddHaarMeasure] (e : H ≃ₜ+ H) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map e = c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  exact ⟨Measure.addHaarScalarFactor (ν.map e) ν,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem map_eq_of_sq_conj (ν : Measure H) [ν.IsAddHaarMeasure] (A B D : H ≃ₜ+ H)
    (h1 : ∀ x, B x = A (A x)) (h2 : ∀ x, B (D x) = D (A x)) : ν.map A = ν := by
  obtain ⟨c, hc0, hc⟩ := exists_scale ν A
  obtain ⟨d, hd0, hd⟩ := exists_scale ν D
  obtain ⟨b, -, hb⟩ := exists_scale ν B
  have mA : Measurable A := A.continuous.measurable
  have mB : Measurable B := B.continuous.measurable
  have mD : Measurable D := D.continuous.measurable
  have e1 : b • ν = (c * c) • ν := by
    rw [← hb]
    have : (B : H → H) = A ∘ A := funext h1
    rw [this, ← Measure.map_map mA mA, hc, Measure.map_smul, hc, smul_smul]
  have e2 : (d * b) • ν = (c * d) • ν := by
    have h3 : (B : H → H) ∘ D = D ∘ A := funext h2
    have l : (ν.map D).map B = (d * b) • ν := by
      rw [hd, Measure.map_smul, hb, smul_smul]
    have r : (ν.map A).map D = (c * d) • ν := by
      rw [hc, Measure.map_smul, hd, smul_smul]
    rw [← l, ← r, Measure.map_map mB mD, Measure.map_map mD mA, h3]
  obtain ⟨Kc, hK, hKn⟩ := exists_compact_mem_nhds (0 : H)
  have hpos : ν Kc ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have htop : ν Kc ≠ ⊤ := hK.measure_lt_top.ne
  have cancel : ∀ u v : ℝ≥0, u • ν = v • ν → u = v := by
    intro u v h
    have := congrArg (fun m : Measure H => m Kc) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 this
  have hb' := cancel _ _ e1
  have hcd := cancel _ _ e2
  have hc1 : c = 1 := by
    rw [hb'] at hcd
    have : (c * d) * c = (c * d) * 1 := by
      calc (c * d) * c = d * (c * c) := by ring
        _ = c * d := hcd
        _ = (c * d) * 1 := (mul_one _).symm
    exact mul_left_cancel₀ (mul_ne_zero hc0 hd0) this
  rw [hc, hc1, one_smul]

end Gen

section Mat

local notation "cTr" => HeckeCharacterZeroLocus.SiegelWeilU.cT

variable {K : Type} [CommRing K] (s : K →+* K) {n : ℕ}

theorem cT_one : cTr s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem conj_conj (g h S : Matrix (Fin n) (Fin n) K) :
    cTr s h * (cTr s g * S * g) * h = cTr s (g * h) * S * (g * h) := by
  rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul]
  simp only [Matrix.mul_assoc]

theorem shearM_zero (a : Fin n) : shearM a (0 : Fin n → K) = 1 := by
  ext i j
  simp [shearM]

theorem shearM_mul (a : Fin n) (x y : Fin n → K) (hy : y a = 0) :
    shearM a x * shearM a y = shearM a (x + y) := by
  have hN : (Matrix.of (fun b c => if c = a then x b else 0) *
      Matrix.of (fun b c => if c = a then y b else 0) : Matrix (Fin n) (Fin n) K) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = a
    · subst hk
      by_cases hj : j = k <;> simp [hj, hy]
    · simp [hk]
  rw [shearM, shearM, shearM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hN, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, add_zero]
  ext i j
  by_cases hj : j = a
  · simp [hj]
    ring
  · simp [hj]

def diagAt (a : Fin n) (t : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i => if i = a then t else 1

theorem diagAt_mul (a : Fin n) (t u : K) (h : t * u = 1) : diagAt a t * diagAt a u = 1 := by
  rw [diagAt, diagAt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = a <;> simp [hi, h]

theorem diagAt_shearM (a : Fin n) (x : Fin n → K) (hx : x a = 0) :
    diagAt a 2 * shearM a (x + x) = shearM a x * diagAt a 2 := by
  ext i j
  rw [diagAt, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [shearM, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  by_cases hj : j = a
  · subst hj
    by_cases hi : i = j
    · subst hi
      simp [hx]
    · simp [Matrix.one_apply, hi] <;> ring
  · by_cases hij : i = j
    · subst hij
      simp [hj]
    · rw [Matrix.one_apply_ne hij]
      simp [hj]

variable [TopologicalSpace K] [IsTopologicalRing K]

def conjEq (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cTr s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) : H ≃ₜ+ H where
  toFun S := ⟨cTr s g * S * g, hH _ S.2 g⟩
  invFun S := ⟨cTr s g' * S * g', hH _ S.2 g'⟩
  left_inv S := Subtype.ext (by
    change cTr s g' * (cTr s g * (S : Matrix (Fin n) (Fin n) K) * g) * g' = S
    rw [conj_conj, h1, cT_one, Matrix.one_mul, Matrix.mul_one])
  right_inv S := Subtype.ext (by
    change cTr s g * (cTr s g' * (S : Matrix (Fin n) (Fin n) K) * g') * g = S
    rw [conj_conj, h2, cT_one, Matrix.one_mul, Matrix.mul_one])
  map_add' S T := Subtype.ext (by
    change cTr s g * ((S : Matrix (Fin n) (Fin n) K) + T) * g = cTr s g * S * g + cTr s g * T * g
    rw [Matrix.mul_add, Matrix.add_mul])
  continuous_toFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

theorem conjEq_val (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cTr s g * S * g ∈ H)
    (g g' : Matrix (Fin n) (Fin n) K) (h1 : g * g' = 1) (h2 : g' * g = 1) (S : H) :
    (conjEq s H hH g g' h1 h2 S : Matrix (Fin n) (Fin n) K) = cTr s g * S * g := rfl

theorem map_shear (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ H, ∀ g : Matrix (Fin n) (Fin n) K, cTr s g * S * g ∈ H)
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsAddHaarMeasure] (h2 : IsUnit (2 : K)) (a : Fin n) (x : Fin n → K) (hx : x a = 0)
    (τ : H → H) (hτ : ∀ S, (τ S : Matrix (Fin n) (Fin n) K) = cTr s (shearM a x) * S * shearM a x) :
    ν.map τ = ν := by
  have inv : ∀ y : Fin n → K, y a = 0 → shearM a y * shearM a (-y) = 1 ∧ shearM a (-y) * shearM a y = 1 := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [shearM_mul a _ _ (by simp [hy]), add_neg_cancel, shearM_zero]
    · rw [shearM_mul a _ _ hy, neg_add_cancel, shearM_zero]
  have hxx : (x + x) a = 0 := by simp [hx]
  obtain ⟨i1, i2⟩ := inv x hx
  obtain ⟨j1, j2⟩ := inv (x + x) hxx
  have d1 : diagAt a (2 : K) * diagAt a ((h2.unit⁻¹ : Kˣ) : K) = 1 :=
    diagAt_mul a _ _ (h2.mul_val_inv)
  have d2 : diagAt a ((h2.unit⁻¹ : Kˣ) : K) * diagAt a (2 : K) = 1 :=
    diagAt_mul a _ _ (h2.val_inv_mul)
  have hτe : τ = conjEq s H hH _ _ i1 i2 := funext fun S => Subtype.ext (hτ S)
  rw [hτe]
  refine map_eq_of_sq_conj ν _ (conjEq s H hH _ _ j1 j2) (conjEq s H hH _ _ d1 d2) ?_ ?_
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conj_conj, shearM_mul a _ _ hx]
  · intro S
    apply Subtype.ext
    rw [conjEq_val, conjEq_val, conjEq_val, conjEq_val, conj_conj, conj_conj, diagAt_shearM a x hx]

end Mat

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar

theorem coordHerm_map_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  intro F E _ _ _ _ _ σ hσ n d b lam hlam a s hs τ _ hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hH n
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x : Ainf F ⊗[F] E, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ x) = x :=
    GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol (Ainf F) (GlobalTheory.CompanionTheory.SW.GramAlg.sigma_invol hσ)
  have hmem : ∀ S ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, ∀ g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n := by
    intro S hS g
    have hS' : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) S = S := by
      ext i j
      exact hS i j
    have key : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ)
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g)
        = HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) g * S * g := by
      rw [HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, GlobalTheory.CompanionTheory.SW.GramAlg.cT_cT _ hinv, hS', Matrix.mul_assoc]
    intro i j
    exact congrFun (congrFun key i) j
  have h2 : IsUnit (2 : Ainf F ⊗[F] E) := by
    have : IsUnit (algebraMap F (Ainf F ⊗[F] E) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
    rwa [map_ofNat] at this
  exact map_shear (HeckeCharacterZeroLocus.SiegelWeilU.sigR (Ainf F) σ) (HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n) hmem
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) h2 a s hs τ hτ

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar
