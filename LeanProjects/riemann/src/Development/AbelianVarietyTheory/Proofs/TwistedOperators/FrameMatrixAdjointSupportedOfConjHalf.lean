import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupp

theorem smul_mul_mul_of_smul_eq {R : Type} [CommRing R] {a b c d : Type} [Fintype b] [Fintype c]
    (r : R) (A : Matrix a b R) (N : Matrix b c R) (B : Matrix c d R) (h : r • N = N) :
    r • (A * N * B) = A * N * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem map_smul_of_smul_eq {R S : Type} [CommRing R] [CommRing S] {a b : Type} (f : R →+* S)
    (r : R) (N : Matrix a b R) (h : r • N = N) : f r • N.map f = N.map f := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1
  simpa [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h k) l

theorem frMapAdj_supp : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  intro D S T βS βT e x he hx i j
  have hN : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
    have h1 := hx l k
    have h2 : cA D (x l k) = e * cA D (x l k) := by
      conv_lhs => rw [← h1]
      rw [map_mul, cA_cA]
    exact h2.symm
  have hM := smul_mul_mul_of_smul_eq e ((S.gram⁻¹).map (incA D)) _ (T.gram.map (incA D)) hN
  have hM' := map_smul_of_smul_eq (toEAf D) e _ hM
  have hF := smul_mul_mul_of_smul_eq (toEAf D e) (βS⁻¹).val _ βT.val hM'
  have := congrFun (congrFun hF i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.HalfSupp
