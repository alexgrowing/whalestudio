import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormalFormAgree

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

def ChiTors : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (c : (D.fm u).clsP), ∃ k : ℕ, 0 < k ∧
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) ^ k = 1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def tauLE (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def AL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.what₂.LL :=
  (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (tauLE D τ)

def PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL :=
  C (∏ τ, (AL Tf c τ).det ^ shiftOf (lamT u D.R.m) τ) * rowSubK (AL Tf c) F

theorem AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    (AL Tf c τ).map j = (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) *
      bZ u Tf.til.z0).map (embS D j τ) := by
  unfold AL
  rw [Matrix.map_map]
  rfl

theorem map_PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (PL Tf c F) = (∏ τ, ((AL Tf c τ).map j).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => (AL Tf c τ).map j) (map j F) := by
  unfold PL
  rw [map_mul, map_C, map_rowSubK, rowSubK_eq_subP, subP_eq_blkRow, MvPolynomial.smul_eq_C_mul, map_prod]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, RingHom.map_det]
  rfl

theorem isUnit_AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    IsUnit ((AL Tf c τ).map j).det := by
  rw [AL_map, Matrix.map_mul, Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · exact isUnit_det_atInf (embS D j) (((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) τ
  · have := (bZ_isUnitS Tf).map (embS D j τ)
    rw [RingHom.map_det] at this
    exact this

end Formalism.L2.GlobalTheoryTheory.Br
