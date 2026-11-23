import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdjAct

variable {D : D7}

theorem mt_mul_mt_inv (T : HSp D) (g : GA D T) : Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹ = 1 := by
  show (matHom T g).1 * (matHom T g⁻¹).1 = 1
  rw [map_inv]; exact (matHom T g).mul_inv

theorem mt_one_inv (S : HSp D) : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
  show (matHom S 1⁻¹).1 = 1
  simp

theorem cT_mt_gram (T : HSp D) (g : GA D T) : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) =
    T.gram.map (incA D) * Formalism.L2.Theta.mt T g⁻¹ := by
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) * Formalism.L2.Theta.mt T g =
      T.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) *
        (Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹) := by rw [mt_mul_mt_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hU]

theorem finE_inv_val (T : HSp D) (g : GA D T) :
    ((Formalism.IndefR.Lev.finE T g)⁻¹).1 = (Formalism.L2.Theta.mt T g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val {n : ℕ} (β y : GL (Fin n) (EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem conj_transpose_mul (S T : HSp D) (g : GA D T) (x : WO S T) :
    ((HMul.hMul (Formalism.L2.Theta.mt T g) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      HMul.hMul ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ
        (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem assoc_swap {R : Type} [CommRing R] {s t : ℕ} (A : Matrix (Fin s) (Fin s) R) (X : Matrix (Fin s) (Fin t) R)
    (C G N : Matrix (Fin t) (Fin t) R) (h : C * G = G * N) : A * (X * C) * G = A * X * G * N := by
  simp only [Matrix.mul_assoc]
  rw [h]

theorem frame_assoc {R : Type} [CommRing R] {s t : ℕ} (bS : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (N bT bTi : Matrix (Fin t) (Fin t) R) (hb : bT * bTi = 1) :
    bS * (Y * N) * bT = bS * Y * bT * (bTi * N * bT) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bT, hb, Matrix.one_mul]

theorem frMapAdj_actO : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D S T βS βT g x
  rw [frMapAdj, frMapAdj, actO, mt_one_inv, Matrix.mul_one, conj_transpose_mul, conj_inv_val, finE_inv_val,
    assoc_swap _ _ _ _ _ (cT_mt_gram T g), Matrix.map_mul]
  exact frame_assoc _ _ _ _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

end GlobalTheory.AdjAct
