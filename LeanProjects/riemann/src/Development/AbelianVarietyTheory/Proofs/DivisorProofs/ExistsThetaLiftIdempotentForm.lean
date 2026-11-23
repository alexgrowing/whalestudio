import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitaryMove

section Generic

variable {A : Type} [CommRing A] {n : ℕ} (c : A →+* A)

def ct (X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := (X.map c).transpose

theorem ct_add (X Y : Matrix (Fin n) (Fin n) A) : ct c (X + Y) = ct c X + ct c Y := by
  simp only [ct, Matrix.map_add _ (map_add c), Matrix.transpose_add]

theorem ct_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : ct c (a • X) = c a • ct c X := by
  ext i j
  simp [ct]

theorem ct_one : ct c (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  rw [ct, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem ct_mul (X Y : Matrix (Fin n) (Fin n) A) : ct c (X * Y) = ct c Y * ct c X := by
  rw [ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

theorem ct_ct (hc : ∀ a, c (c a) = a) (X : Matrix (Fin n) (Fin n) A) : ct c (ct c X) = X := by
  ext i j
  exact hc _

theorem blockUnit (hc : ∀ a, c (c a) = a) {e : A} (he : e * e = e) (he' : e * c e = 0)
    (P Q : Matrix (Fin n) (Fin n) A) (hPQ : e • (P * Q) = e • (1 : Matrix (Fin n) (Fin n) A))
    (hQP : e • (Q * P) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) = 1 ∧
      ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) = 1 ∧
      ct c ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) =
        (1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  have hsum : f + e + c e = 1 := by rw [hf]; ring
  have hPQ' : c e • (ct c Q * ct c P) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hPQ, ct_smul, ct_one]
  have hQP' : c e • (ct c P * ct c Q) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hQP, ct_smul, ct_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hPQ, hPQ']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hQP, hQP']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · rw [ct_add, ct_add, ct_smul, ct_smul, ct_smul, ct_one, ct_ct c hc, hcf, hc]
    abel

end Generic

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem exists_blockUnit : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  intro D V hV e he he' P Q hPQ hQP
  obtain ⟨h1, h2, h3⟩ := blockUnit (cA D) cA_cA he he' P Q hPQ hQP
  have hmem : (((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q).map (cA D)).transpose *
      V.gram.map (incA D) * ((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q) =
      V.gram.map (incA D) := by
    rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact (congrArg (· * _) h3).trans h2
  let u : GL (Fin V.rank) (AE D) := ⟨_, _, h1, h2⟩
  have hu : u ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram := hmem
  let g : GA D V := (⟨u, hu⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hg : Formalism.L2.Theta.mt V g = u.1 := rfl
  have hg' : Formalism.L2.Theta.mt V g⁻¹ = u⁻¹.1 := rfl
  exact ⟨g, hg, hg'⟩
end GlobalTheory.UnitaryMove
