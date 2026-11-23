import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFramesCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Lifts

namespace FLW

variable {n : ℕ}

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (u u' w : Fin n → ℂ) :
    herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (u w w' : Fin n → ℂ) :
    herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem unitary_of_herm (H M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ u v, herm H (M *ᵥ u) (M *ᵥ v) = herm H u v) :
    Mᴴ * H * M = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, Matrix.mulVec_single_one] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  convert this using 1
  · simp [dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]

end FLW

theorem wittHpk (k r : ℕ) {ι : Type} [Fintype ι] (x y : ι → Fin (2 * r + k + 1) → ℂ)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hg : ∀ i j, herm (Hpk k r) (x i) (x j) = herm (Hpk k r) (y i) (y j)) :
    ∃ g ∈ B.GV k r, ∀ i, g *ᵥ x i = y i := by
  set H := Hpk k r with hHdef
  have hHh : Hᴴ = H := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hHH : H * H = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  let Bf : (Fin (2 * r + k + 1) → ℂ) →ₗ⋆[ℂ] (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun u v => herm H v u)
      (fun u u' v => FLW.herm_add_r H v u u')
      (fun c u v => by rw [FLW.herm_smul_r, smul_eq_mul]; rfl)
      (fun u v v' => FLW.herm_add_l H v v' u)
      (fun c u v => by rw [FLW.herm_smul_l, smul_eq_mul]; rfl)
  have hB : ∀ u v, Bf u v = herm H v u := fun u v => rfl
  have hsym : ∀ a b, star (Bf a b) = Bf b a := by
    intro a b
    rw [hB, hB, ggHerm_swap H hHh a b]
  have hnd : ∀ a, (∀ b, Bf a b = 0) → a = 0 := by
    intro a ha
    have h0 := ha (H *ᵥ a)
    rw [hB] at h0
    simp only [herm, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec] at h0
    have h1 : ∑ i, Complex.normSq (a i) = 0 := by
      have : (∑ i, Complex.normSq (a i) : ℂ) = star a ⬝ᵥ a := by
        simp [dotProduct, Complex.mul_conj, mul_comm]
      exact_mod_cast this.trans h0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (a j))).1 h1 i (Finset.mem_univ _)
    simpa using this
  let U := Submodule.span ℂ (Set.range x)
  let bU : Module.Basis ι ℂ U := Module.Basis.span hx
  have hbU : ∀ a, (bU a : Fin (2 * r + k + 1) → ℂ) = x a := fun a => by
    show ((Module.Basis.span hx a : U) : Fin (2 * r + k + 1) → ℂ) = x a
    rw [Module.Basis.span_apply]
  let f : U →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) := bU.constr ℂ y
  have hf : ∀ a, f (bU a) = y a := fun a => bU.constr_basis ℂ y a
  have hfsum : ∀ u : U, f u = ∑ a, bU.repr u a • y a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [map_sum]; simp only [map_smul, hf]
  have husum : ∀ u : U, (u : Fin (2 * r + k + 1) → ℂ) = ∑ a, bU.repr u a • x a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [Submodule.coe_sum]; simp only [Submodule.coe_smul, hbU]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hfsum] at hu
    have hc := Fintype.linearIndependent_iff.mp hy _ hu
    have : bU.repr u = 0 := by ext a; simp [hc a]
    simpa using this
  have hsum_l : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H (∑ a, c a • v a) w = ∑ a, c a * herm H (v a) w := by
    intro c v w
    simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have hsum_r : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H w (∑ a, c a • v a) = ∑ a, star (c a) * herm H w (v a) := by
    intro c v w
    simp [herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hisom : ∀ u v : U, Bf (f u) (f v) = Bf u v := by
    intro u v
    rw [hB, hB, hfsum, hfsum, husum, husum, hsum_l, hsum_l]
    apply Finset.sum_congr rfl; intro a _
    rw [hsum_r, hsum_r]
    congr 1
    apply Finset.sum_congr rfl; intro b _
    rw [hg]
  obtain ⟨g, hgB, hgf⟩ := _root_.witt_extension_theorem ℂ (Fin (2 * r + k + 1) → ℂ) Bf hsym hnd U f hinj hisom
  refine ⟨LinearMap.toMatrix' (g : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ)), ?_, fun i => ?_⟩
  · show _ * H * _ = H
    apply FLW.unitary_of_herm
    intro u v
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    have := hgB v u
    rw [hB, hB] at this
    exact this
  · rw [LinearMap.toMatrix'_mulVec]
    have := hgf (bU i)
    rw [hbU, hf] at this
    exact this

end PI.UnitaryGroupMassFormula.DLm.Lifts
