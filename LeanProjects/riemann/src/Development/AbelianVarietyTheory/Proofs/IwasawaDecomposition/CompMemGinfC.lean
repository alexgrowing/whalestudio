import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocWeil.CompactPart

theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ Formalism.UG.Jpq p q * b = b * Formalism.UG.Jpq p q := by
  rw [← Matrix.fromBlocks_toBlocks b]
  generalize b.toBlocks₁₁ = a, b.toBlocks₁₂ = c, b.toBlocks₂₁ = d, b.toBlocks₂₂ = e
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, true_and, and_true]
  constructor
  · intro h
    have hc : c = 0 := by
      ext i j
      exact h (.inl i) (.inr j) (by simp [sameBlock])
    have hd : d = 0 := by
      ext i j
      exact h (.inr i) (.inl j) (by simp [sameBlock])
    simp [hc, hd]
  · rintro ⟨h1, h2⟩ x y hxy
    rcases x with i | i <;> rcases y with j | j
    · simp [sameBlock] at hxy
    · have := congrFun (congrFun h1 i) j
      simp only [Matrix.neg_apply] at this
      show c i j = 0
      linear_combination this / 2
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.neg_apply] at this
      show d i j = 0
      linear_combination -this / 2
    · simp [sameBlock] at hxy

theorem isKC_one {p q : ℕ} : IsKC (1 : Mat p q) := by
  rw [isKC_iff, Matrix.one_mul, Matrix.mul_one]

theorem isKC_mul {p q : ℕ} {a b : Mat p q} (ha : IsKC a) (hb : IsKC b) : IsKC (a * b) := by
  rw [isKC_iff] at *
  rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]

theorem isKC_inv {p q : ℕ} {a b : Mat p q} (ha : IsKC a) (h : a * b = 1) : IsKC b := by
  rw [isKC_iff] at *
  have h' : b * a = 1 := mul_eq_one_comm.1 h
  calc Formalism.UG.Jpq p q * b = b * a * Formalism.UG.Jpq p q * b := by rw [h', Matrix.one_mul]
    _ = b * Formalism.UG.Jpq p q * (a * b) := by
      rw [Matrix.mul_assoc b a, ← ha]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.mul_one]

variable {D : D7}

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem infMat_mul' (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * g') = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ g' := by
  rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]

theorem infMat_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V} (hk : k ∈ GfC V) :
    infMat D.sp.cm.sig V.gram θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_inv {V : HSp D} (hV : V.SigOK) {τ : D.what₂.Tau}
    {A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = gramAt D V τ) :
    ∃ B : Matrix (Fin V.rank) (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) ℂ, B * A = 1 ∧ A * B = 1 := by
  have hd : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := ((tauE D τ).map_det V.gram).symm
    rw [this, isUnit_iff_ne_zero]
    exact (map_ne_zero _).2 (GlobalTheory.LocWCompare.gram_det_ne V)
  have h1 : ((gramAt D V τ)⁻¹ * (Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2)) * A = 1 := by
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ hd]
  have hc := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
  refine ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ ?_).1 h1⟩
  simp only [Fintype.card_fin, Fintype.card_sum] at hc ⊢
  omega

def kinf (θ : InfF D) {V : HSp D} (A : CptF V) (hV : V.SigOK)
    (hA : ∀ τ, (A τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A τ = gramAt D V τ) :
    Subgroup (GA D V) where
  carrier := {k | IsKinf θ V A k}
  one_mem' := ⟨one_mem _, fun τ => ⟨1, isKC_one, by
    rw [infMat_of_fin V _ (one_mem _), Matrix.one_mul, Matrix.mul_one]⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨mul_mem g1 h1, fun τ => ?_⟩
    obtain ⟨a, ha, ea⟩ := g2 τ
    obtain ⟨b, hb, eb⟩ := h2 τ
    refine ⟨a * b, isKC_mul ha hb, ?_⟩
    rw [infMat_mul', Matrix.mul_assoc, eb, ← Matrix.mul_assoc, ea, Matrix.mul_assoc]
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    refine ⟨inv_mem g1, fun τ => ?_⟩
    obtain ⟨a, ha, ea⟩ := g2 τ
    obtain ⟨B, hB, hB'⟩ := exists_inv hV (hA τ)
    refine ⟨A τ * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ * B, isKC_inv ha ?_, ?_⟩
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ea, Matrix.mul_assoc (A τ), ← infMat_mul', mul_inv_cancel,
        infMat_of_fin V _ (one_mem _), Matrix.mul_one, hB']
    · rw [Matrix.mul_assoc, hB, Matrix.mul_one]

end GlobalTheory.LocWeil.CompactPart

end
