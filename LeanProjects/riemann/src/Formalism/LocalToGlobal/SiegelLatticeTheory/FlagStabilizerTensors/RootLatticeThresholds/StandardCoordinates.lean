import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotientSpan

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.StandardCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u' : D.what₂.Word)

include hT in

theorem fam_eq (hl : lam ≠ 0) (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u' 1 v b =
      (lam ^ (D.R.rS - b.val))⁻¹ • (Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun c => ?_) b
  · rw [Fin.snoc_last]
    unfold Formalism.QuantumDeterminants.fvec
    rw [dif_neg (by simp), Matrix.mulVec_mulVec, hT.2.1, Matrix.one_mulVec, Fin.val_last, Nat.sub_self, pow_zero,
      inv_one, one_smul]
  · rw [Fin.snoc_castSucc]
    have h1 := (hT.2.2.2 c c rfl).1
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]

include hT hl in

theorem stCoordV_gen (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v))
    (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y p =
      ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.1.1) / ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.2.1) *
      ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have ha : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
    intro h; rw [h, mul_zero] at this; exact zero_ne_one this
  set z' := Qi *ᵥ rv X.B.I v (X.zR u') with hz'
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS z' p.1.2 with hf
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val))⁻¹ • ((lam ^ (D.R.rS - p.1.2.val))⁻¹ • (Q *ᵥ f)) := by
    rw [← fam_eq v hT u' hl p.1.2]
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  have hfR : rv X.B.I v (X.fR ⟨p.1.1.1, ha⟩) =
      star (lam ^ (D.R.rS - p.1.1.1)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨p.1.1.1, ha⟩) 1) := by
    rw [(hT.2.2.2 ⟨p.1.1.1, ha⟩ ⟨p.1.1.1, ha⟩ rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
    exact star_ne_zero.2 (pow_ne_zero _ hl)
  have hM : uMat ((γ v)⁻¹ * y * γ v) *ᵥ (Q *ᵥ f) = Q *ᵥ ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, hQQi, Matrix.one_mul]
  have hQ : ∀ x v' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      star (Q *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (Q *ᵥ v')) = star x ⬝ᵥ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *ᵥ v') := by
    intro x v'
    rw [← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
  unfold Formalism.L2.SG.NGPin.stCoordV
  rw [hfrm, hfR, Matrix.mulVec_smul, Matrix.mulVec_smul, hM]
  unfold hJ
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, star_smul, smul_dotProduct, hQ,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI]
  simp only [smul_eq_mul, star_star]
  have h1 : (lam ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hl
  have h2 : ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hrd
  rw [mul_pow, mul_pow]
  field_simp

include hT hl in

theorem coord_conj (M H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hHU : Hᴴ * Formalism.REAL.Jm (X.B.I.ε v) * H = Formalism.REAL.Jm (X.B.I.ε v)) (hHu : IsUnit H.det)
    (he : ∀ b, H *ᵥ rv X.B.I v (X.eR b) = rv X.B.I v (X.eR b)) (hz : H *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u'))
    (hfa : ∀ a, H *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ((Qi * (H⁻¹ * M * H) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      ((Qi * M * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b with hf

  have hHf : H *ᵥ (Q *ᵥ f) = Q *ᵥ f := by
    have := fam_eq v hT u' hl b
    have e : Q *ᵥ f = lam ^ (D.R.rS - b.val) • Formalism.L2.SG.RealObj.frm X u' 1 v b := by
      rw [this, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
    rw [e, Matrix.mulVec_smul]
    congr 1
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact he c

  have hread : ∀ x : Fin X.B.I.n → ℂ, (Qi *ᵥ x) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      (lam ^ (D.R.rS - a.val))⁻¹ * hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hfR : rv X.B.I v (X.fR a) = star (lam ^ (D.R.rS - a.val)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [(hT.2.2.2 a a rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
      exact star_ne_zero.2 (pow_ne_zero _ hl)
    have hx : x = Q *ᵥ (Qi *ᵥ x) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [hfR]
    conv_rhs => rw [hx]
    unfold hJ
    rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
      Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI, smul_eq_mul, star_star,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl), one_mul]
  have hisom : ∀ x y : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (H *ᵥ x) (H *ᵥ y) = hJ (X.B.I.ε v) x y := by
    intro x y
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' H x (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (H *ᵥ y)), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hHU]
  have hinvJ : ∀ x : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (H⁻¹ *ᵥ x) =
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hx : H *ᵥ (H⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hHu, Matrix.one_mulVec]
    rw [← hisom, hfa a, hx]
  have e1 : (Qi * (H⁻¹ * M * H) * Q) *ᵥ f = Qi *ᵥ (H⁻¹ *ᵥ (M *ᵥ (Q *ᵥ f))) := by
    simp only [← Matrix.mulVec_mulVec, hHf]
  have e2 : (Qi * M * Q) *ᵥ f = Qi *ᵥ (M *ᵥ (Q *ᵥ f)) := by
    simp only [← Matrix.mulVec_mulVec]
  rw [e1, e2, hread, hread, hinvJ]

end Formalism.L2.SG.StandardCoordinates

end
