import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.OrthogonalFormMulTranspose

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

theorem unitary_group_inverse_formula (g : M2 n) (hg : InG g) : -(JJ n * gᴴ * JJ n) * g = 1 := by
  have hg' : gᴴ * JJ n * g = JJ n := hg
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', JJ_sq, neg_neg]

def mkG (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, -(JJ n * gᴴ * JJ n), mul_eq_one_comm.1 (unitary_group_inverse_formula g hg), unitary_group_inverse_formula g hg⟩, hg⟩

theorem mR_mkG (g : M2 n) (hg : InG g) : mR (mkG g hg) = g := rfl

def phi (ζ : ℂ) (h : M2 n) : M2 n := dZ n ζ * h * dZ n ζ⁻¹

theorem inG_phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) {h : M2 n} (hh : InU (Qc n ε)ᵀ h) :
    InG (phi ζ h) :=
  inG_conj hζ h ((inU_iff ε h).1 hh)

def Phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (h : {h : M2 n // InU (Qc n ε)ᵀ h}) : GR n :=
  mkG (phi ζ h.1) (inG_phi hζ h.2)

theorem continuous_Phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    Continuous (Phi (n := n) hζ) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun h : {h : M2 n // InU (Qc n ε)ᵀ h} => phi ζ h.1
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  · show Continuous fun h : {h : M2 n // InU (Qc n ε)ᵀ h} => -(JJ n * (phi ζ h.1)ᴴ * JJ n)
    exact ((continuous_const.matrix_mul (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
      continuous_const).matrix_conjTranspose)).matrix_mul continuous_const).neg

theorem Phi_surj {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (y : GR n) :
    ∃ h : {h : M2 n // InU (Qc n ε)ᵀ h}, Phi hζ h = y := by
  refine ⟨⟨dZ n ζ⁻¹ * mR y * dZ n ζ, (inU_iff ε _).2 ((unitary_iff hζ (mR y)).2 y.2)⟩, ?_⟩
  have h0 := zeta_ne hζ
  apply Subtype.ext
  apply Units.ext
  show dZ n ζ * (dZ n ζ⁻¹ * mR y * dZ n ζ) * dZ n ζ⁻¹ = mR y
  simp only [← Matrix.mul_assoc, dZ_mul_inv h0, Matrix.one_mul]
  rw [Matrix.mul_assoc, dZ_mul_inv h0, Matrix.mul_one]

theorem exists_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (τ : E →+* ℂ) {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) {O : Set (GR n)}
    (hO : IsOpen O) {y : GR n} (hy : y ∈ O) :
    ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) (hX : InU (Qc n ε)ᵀ (X.map τ)), Phi hζ ⟨X.map τ, hX⟩ ∈ O := by
  obtain ⟨h0, rfl⟩ := Phi_surj hζ y
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 (hO.preimage (continuous_Phi hζ))
  have h0V : h0.1 ∈ V := by
    have : h0 ∈ Subtype.val ⁻¹' V := by rw [hVe]; exact hy
    exact this
  obtain ⟨X, hXV, hXU⟩ := dense_pts hcm τ ε hV h0V h0.2
  refine ⟨X, hXU, ?_⟩
  have : (⟨X.map τ, hXU⟩ : {h : M2 n // InU (Qc n ε)ᵀ h}) ∈ Subtype.val ⁻¹' V := hXV
  rw [hVe] at this
  exact this

end PositivityTheory.SiegelWeilFormula.Krd.DM

end
