import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.Emat

open Matrix

theorem gram_of_orth {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) (hCo : IsOrthCo σ J co) :
    star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J := by
  ext i k
  have h := hCo (Pi.single i 1) (Pi.single k 1)
  rw [Matrix.mul_apply]
  have hl : ∀ a, (star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)))) i a * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) a k =
      σ (co (Pi.single i 1) a) * co (Pi.single k 1) a := by
    intro a
    rw [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, hσ]
    rfl
  rw [Finset.sum_congr rfl fun a _ => hl a, h]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [Pi.single_apply, hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem toMatrix_toLE {E : Type} [Field E] {N : ℕ} (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((toLE γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = γ := by
  ext i j
  simp [toLE, LinearMap.toMatrix'_apply, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem unit_mat' {n N : ℕ} (hk : n = N) {E' : Type} [Field E'] [StarRing E'] (co coi γ J : Matrix (Fin N) (Fin N) E')
    (h1 : star co * co = J) (h2 : star γ * J * γ = J) (h3 : co * coi = 1) :
    (co * γ * coi).submatrix (finCongr hk) (finCongr hk) * star ((co * γ * coi).submatrix (finCongr hk) (finCongr hk)) = 1 := by
  subst hk
  have e2 : ∀ A : Matrix (Fin n) (Fin n) E', A.submatrix (finCongr rfl) (finCongr rfl) = A := fun A => by ext x y; rfl
  rw [e2, mul_eq_one_comm]
  calc star (co * γ * coi) * (co * γ * coi) = star coi * (star γ * (star co * co) * γ) * coi := by
        simp only [star_mul, Matrix.mul_assoc]
    _ = star coi * (star co * co) * coi := by rw [h1, h2]
    _ = star (co * coi) * (co * coi) := by simp only [star_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h3, star_one, Matrix.one_mul]

theorem star_eq_cT {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    star M = cT σ M := by
  ext i k
  simp [cT, Matrix.star_apply, hσ]

theorem orth_of_gram {E : Type} [Field E] (σ : E →+* E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hM : cT σ (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J) :
    IsOrthCo σ J co := by
  intro x y
  set M := LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) with hMdef
  have hx : ∀ z, co z = M *ᵥ z := fun z => by rw [hMdef, LinearMap.toMatrix'_mulVec]; rfl
  rw [← hM]
  simp only [hx, Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem toMatrix_stdG {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((stdG σ J γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) =
      LinearMap.toMatrix' ((stdCo σ J : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) * (γ : Matrix (Fin N) (Fin N) E) *
        LinearMap.toMatrix' (((stdCo σ J).symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) := by
  rw [← toMatrix_toLE γ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  rfl

theorem toMatrix_co_mul_symm {E : Type} [Field E] {N : ℕ} (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) * LinearMap.toMatrix' ((co.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

end GlobalTheory.TwV.Xc.Emat

end

open GlobalTheory.TwV.Xc.Emat in

theorem GlobalTheory.TwV.Xc.eMat_unitary_det : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (σ : E →+* E), (∀ x, σ x = star x) → ∀ (a N : ℕ) (hr : a = N) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E), cT σ crd.1 * crd.1 = J → IsOrthCo σ J (stdCo σ J) ∧ ∀ g ∈ UJ σ J, eMat hr σ J g * star (eMat hr σ J g) = 1 ∧ (eMat hr σ J g).det = g.1.det := by
  intro E _ _ _ σ hσ a N hr J crd hcrd
  subst hr
  have hco : IsOrthCo σ J (stdCo σ J) := by
    refine Classical.epsilon_spec (p := IsOrthCo σ J) ⟨toLE crd, ?_⟩
    refine orth_of_gram σ J _ ?_
    rw [toMatrix_toLE]
    exact hcrd
  refine ⟨hco, fun g hg => ?_⟩
  have hg' : star (g : Matrix (Fin a) (Fin a) E) * J * (g : Matrix (Fin a) (Fin a) E) = J := by
    rw [star_eq_cT σ hσ]
    exact hg
  unfold eMat
  rw [toMatrix_stdG]
  refine ⟨unit_mat' rfl _ _ _ J (gram_of_orth σ hσ J _ hco) hg' (toMatrix_co_mul_symm _), ?_⟩
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, toMatrix_co_mul_symm,
    Matrix.det_one, one_mul]
