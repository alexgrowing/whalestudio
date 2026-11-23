import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PClsNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.ClsEqP

variable {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]

def psi (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) : B[X] →+* Matrix (Fin n) (Fin n) k :=
  Polynomial.eval₂RingHom' ρ (s • (1 : Matrix (Fin n) (Fin n) k)) (fun a => (Commute.one_right (ρ a)).smul_right s)

theorem psi_C (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (a : B) : psi ρ s (C a) = ρ a :=
  Polynomial.eval₂_C _ _

theorem psi_X (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) : psi ρ s X = s • (1 : Matrix (Fin n) (Fin n) k) :=
  Polynomial.eval₂_X _ _

theorem psi_P (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v : B) :
    psi ρ s (C u + X * C v) = ρ u + s • ρ v := by
  rw [map_add, map_mul, psi_C, psi_X, psi_C, Matrix.smul_mul, Matrix.one_mul]

theorem psi_Q (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v : B) :
    psi ρ s (C u - X * C v) = ρ u - s • ρ v := by
  rw [map_sub, map_mul, psi_C, psi_X, psi_C, Matrix.smul_mul, Matrix.one_mul]

theorem psi_rel {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k)) :
    psi ρ s (X ^ 2 - C d) = 0 := by
  rw [map_sub, map_pow, psi_X, psi_C, hd, _root_.smul_pow, one_pow, sub_self]

theorem psi_eq {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (F G H : B[X]) (h : F = G + (X ^ 2 - C d) * H) : psi ρ s F = psi ρ s G := by
  rw [h, map_add, map_mul, psi_rel hd, zero_mul, add_zero]

theorem GA {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (u v a : B) : (ρ u + s • ρ v) * ρ a * (ρ u - s • ρ v) = ρ ((u ^ 2 - d * v ^ 2) * a) := by
  rw [← psi_P, ← psi_Q, ← psi_C ρ s a, ← psi_C ρ s ((u ^ 2 - d * v ^ 2) * a), ← map_mul, ← map_mul]
  exact psi_eq hd _ _ (C (- v ^ 2 * a)) (by simp only [map_mul, map_sub, map_pow, map_neg]; ring)

theorem AG {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (u v a : B) : (ρ u - s • ρ v) * ρ a * (ρ u + s • ρ v) = ρ ((u ^ 2 - d * v ^ 2) * a) := by
  rw [← psi_P, ← psi_Q, ← psi_C ρ s a, ← psi_C ρ s ((u ^ 2 - d * v ^ 2) * a), ← map_mul, ← map_mul]
  exact psi_eq hd _ _ (C (- v ^ 2 * a)) (by simp only [map_mul, map_sub, map_pow, map_neg]; ring)

theorem A_comm (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v a : B) :
    (ρ u - s • ρ v) * ρ a = ρ a * (ρ u - s • ρ v) := by
  rw [← psi_Q, ← psi_C ρ s a, ← map_mul, ← map_mul, mul_comm]

theorem adj_span {c : k →+* k} {δ : GL (Fin n) k} {s : k} {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k}
    (hF : IsFrame c δ s d ρ) (hcs : c s = -s) (u v : B) :
    δ.val * GlobalTheory.Tw.Phi n k * ((ρ u + s • ρ v).map c)ᵀ = (ρ u - s • ρ v) * (δ.val * GlobalTheory.Tw.Phi n k) := by
  have e : ((ρ u + s • ρ v).map c)ᵀ = ((ρ u).map c)ᵀ + (-s) • ((ρ v).map c)ᵀ := by
    ext i j
    simp [hcs]
  rw [e, Matrix.mul_add, Matrix.mul_smul, ← hF.adj, ← hF.adj, Matrix.sub_mul, Matrix.smul_mul, neg_smul,
    sub_eq_add_neg]

theorem A_delta_theta {c : k →+* k} {δ : GL (Fin n) k} {s : k} {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k}
    (hF : IsFrame c δ s d ρ) (hcs : c s = -s) (g : GL (Fin n) k) (u v : B) (hg : g.val = ρ u + s • ρ v) :
    (ρ u - s • ρ v) * (δ.val * (thetaGL n c g).val) = δ.val := by
  rw [ClsNormP.thetaGL_val']
  have hXY : (g.val.map c)ᵀ * ((g⁻¹).val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one c (map_zero c) (map_one c),
      Matrix.transpose_one]
  calc (ρ u - s • ρ v) * (δ.val * (GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ))
      = ((ρ u - s • ρ v) * (δ.val * GlobalTheory.Tw.Phi n k)) * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * GlobalTheory.Tw.Phi n k * ((g.val.map c)ᵀ * ((g⁻¹).val.map c)ᵀ) * (GlobalTheory.Tw.Phi n k)ᵀ := by
        rw [← adj_span hF hcs u v, ← hg]; simp only [Matrix.mul_assoc]
    _ = δ.val := by
        rw [hXY, Matrix.mul_one, Matrix.mul_assoc, ClsNormP.phi_mul_transpose_eq_one, Matrix.mul_one]

end CompanionTheory.Rg.BcB.G3.ClsEqP

namespace CompanionTheory.Rg.BcB.G3

open ClsEqP in
theorem clsEq_pf : ClsEq := by
  intro k _ _ n c hc δ s hs0 hcs B _ d ρ hF t t'
  constructor
  · rintro ⟨g, hg⟩
    have hN := clsNorm_pf k n c hc δ s hs0 hcs B d ρ hF t
    have hN' := clsNorm_pf k n c hc δ s hs0 hcs B d ρ hF t'
    have e : g⁻¹ * pt δ ρ t * thetaGL n c g * thetaGL n c (g⁻¹ * pt δ ρ t * thetaGL n c g) =
        g⁻¹ * (pt δ ρ t * thetaGL n c (pt δ ρ t)) * g := by
      simp only [map_mul, map_inv, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc]; group
    rw [hg, e, hN] at hN'
    have hcomm : g * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * g := by
      calc g * (δ * thetaGL n c δ) = g * (g⁻¹ * (δ * thetaGL n c δ) * g) := by rw [hN']
        _ = (δ * thetaGL n c δ) * g := by group
    obtain ⟨u, v, huv⟩ := hF.span g.val (by simpa only [Units.val_mul] using congrArg Units.val hcomm)
    have hA := A_delta_theta hF hcs g u v huv
    have hg1 : g * pt δ ρ t' = pt δ ρ t * thetaGL n c g := by rw [hg]; group
    have hg2 : g.val * (ρ t' * δ.val) = ρ t * δ.val * (thetaGL n c g).val := by
      simpa only [pt, Units.val_mul, ClsNormP.units_map_val] using congrArg Units.val hg1
    have h3 : ρ ((u ^ 2 - d * v ^ 2) * t') * δ.val = ρ t * δ.val := by
      calc ρ ((u ^ 2 - d * v ^ 2) * t') * δ.val = (ρ u - s • ρ v) * ρ 1 * g.val * (ρ t' * δ.val) := by
            rw [huv, AG hF.sq u v 1, mul_one, map_mul, Matrix.mul_assoc]
        _ = (ρ u - s • ρ v) * (ρ t * δ.val * (thetaGL n c g).val) := by
            rw [map_one, Matrix.mul_one, Matrix.mul_assoc, hg2]
        _ = ρ t * ((ρ u - s • ρ v) * (δ.val * (thetaGL n c g).val)) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, A_comm, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = ρ t * δ.val := by rw [hA]
    have h4 : ρ ((u ^ 2 - d * v ^ 2) * t') = ρ t := by
      have := congrArg (· * (δ⁻¹).val) h3
      simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
    exact ⟨u, v, by rw [← hF.inj h4, mul_comm]⟩
  · rintro ⟨u, v, huv⟩
    set w : Bˣ := t'⁻¹ * t with hwdef
    have hw : (w : B) = u ^ 2 - d * v ^ 2 := by
      rw [hwdef, Units.val_mul, huv, ← mul_assoc, Units.inv_mul, one_mul]
    have h1 : (ρ u + s • ρ v) * ((ρ u - s • ρ v) * ρ (↑w⁻¹ : B)) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_one (ρ u + s • ρ v), ← map_one ρ, GA hF.sq u v 1, ← map_mul, ← hw,
        mul_one, Units.mul_inv]
    have h2 : ((ρ u - s • ρ v) * ρ (↑w⁻¹ : B)) * (ρ u + s • ρ v) = 1 := by
      rw [AG hF.sq u v, ← hw, Units.mul_inv, map_one]
    have h5 : (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * (ρ u - s • ρ v) = 1 := by
      rw [GA hF.sq u v, ← hw, Units.mul_inv, map_one]
    let G : GL (Fin n) k := ⟨ρ u + s • ρ v, (ρ u - s • ρ v) * ρ (↑w⁻¹ : B), h1, h2⟩
    refine ⟨G, ?_⟩
    have hA := A_delta_theta hF hcs G u v rfl
    have hθ : δ.val * (thetaGL n c G).val = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by
      calc δ.val * (thetaGL n c G).val
          = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * (ρ u - s • ρ v) * (δ.val * (thetaGL n c G).val) := by
            rw [h5, Matrix.one_mul]
        _ = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by rw [Matrix.mul_assoc _ (ρ u - s • ρ v), hA]
    have hB : ((w * w⁻¹ * t * w⁻¹ : Bˣ) : B) = t' := by
      congr 1; rw [hwdef]; group
    apply Units.ext
    simp only [pt, Units.val_mul, ClsNormP.units_map_val]
    change ρ t' * δ.val = (ρ u - s • ρ v) * ρ (↑w⁻¹ : B) * (ρ t * δ.val) * (thetaGL n c G).val
    calc ρ (t' : B) * δ.val = ρ ((u ^ 2 - d * v ^ 2) * ((↑w⁻¹ : B) * t) * (↑w⁻¹ : B)) * δ.val := by
          rw [← hw, ← hB]; simp only [Units.val_mul, mul_assoc]
      _ = (ρ u - s • ρ v) * ρ ((↑w⁻¹ : B) * t) * (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by
          rw [AG hF.sq u v, map_mul]
      _ = (ρ u - s • ρ v) * ρ (↑w⁻¹ : B) * (ρ t * δ.val) * (thetaGL n c G).val := by
          rw [Matrix.mul_assoc _ (ρ t * δ.val), Matrix.mul_assoc (ρ t), hθ, map_mul]
          simp only [Matrix.mul_assoc]

end CompanionTheory.Rg.BcB.G3

end
