import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory

open Matrix MvPolynomial Formalism.L2.GlobalTheoryTheory.Br

set_option maxHeartbeats 1000000 in

theorem coMTS_of_gaInv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B' : GL (Fin (D.R.N D.R.m)) D.host.E), IsUnit (B w c).det → (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) * bZg u Tf.til.z0 (B w c) → ∀ (f : (D.mem u).C.Y D.R.m → ℂ) (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ), (∀ z, f z = fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) → Formalism.L2.GlobalTheoryTheory.Br.coMTS Tf B w c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) • P := by
  intro D u Ch chOf Tf B w c B' hBdet hB' f P hf
  have hg : ∃ g : GL (Fin (D.R.N D.R.m)) D.host.E, g = (Tf.til.ga c).1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hg
  rw [← hg] at hB'
  have hbZg := bZg_isUnitS Tf (B w c) hBdet
  have hU2 := atInf_inv_isUnit _ hbZg

  have hprod : ∀ τ, atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ *
      atInf (embT D) ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ =
      atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul]
    congr 1
    have e1 : ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
        (((g * B')⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    have e2 : ((g * B' : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = bZg u Tf.til.z0 (B w c) := by
      rw [Units.val_mul, hB', ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e1, Matrix.coe_units_inv, e2]
  subst hg
  have hT : trEvS Tf c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
      fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
        (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) P := by
    funext y
    simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, hf, Equiv.apply_symm_apply]
    congr 1
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, ← Matrix.mul_assoc, hprod]
  simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
  rw [hT, map_smul, fnInv_fnOf _ _ _ hU2]

end GlobalTheory
