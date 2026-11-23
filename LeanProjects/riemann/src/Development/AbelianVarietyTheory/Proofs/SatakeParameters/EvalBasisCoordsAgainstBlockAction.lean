import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem substR_substR (R : Type) [CommRing R] (G G' : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (Q : XR P R) : substR P R G (substR P R G' Q) = substR P R (fun v s => G' v s * G v s) Q := by
  have hc : (substR P R G).comp (substR P R G') = substR P R (fun v s => G' v s * G v s) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [AlgHom.comp_apply, substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  exact congrArg (fun φ : XR P R →ₐ[R] XR P R => φ Q) hc

theorem natActR_natActR (R : Type) [Field R] (g g' : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    natActR P R g (natActR P R g' Q) = natActR P R (fun v s => g v s * g' v s) Q := by
  unfold natActR
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, substR_substR]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_mul, Matrix.det_mul, mul_zpow, mul_comm]

theorem natActR_one (R : Type) [Field R] (Q : XR P R) : natActR P R (fun _ _ => 1) Q = Q := by
  have hs : substR P R (fun _ _ => 1) = AlgHom.id R (XR P R) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
    simp [ite_mul, Finset.sum_ite_eq]
  unfold natActR
  simp only [inv_one, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hs]
  rfl

end Act

theorem invT_mul {k : Type} [Fintype k] [DecidableEq k] (A B : GL k ℂ) : invT (A * B) = invT A * invT B := by
  ext : 1
  simp only [invT, Units.val_mk, Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_one {k : Type} [Fintype k] [DecidableEq k] : invT (1 : GL k ℂ) = 1 := by
  ext : 1
  simp [invT]

variable {p : ℕ} [Fact p.Prime]

theorem evC_crdB_actC (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E)
    (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n)
    (hf : ∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) :
    evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧
      actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  have hcr : ∀ τ, crdB (embT D) B τ = (atR D B⁻¹ τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => rfl
  let y : Fr1 D n := ⟨fun τ => crdB (embT D) B τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul, hcr]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (atR D B⁻¹ τ).isUnit).mul (z.2 τ)⟩
  refine ⟨?_, ?_⟩
  · have hz : ∀ v s, zAt (X.Pj i) h (posJ X D pos i) (crdB (embT D) B) z.1 v s =
        zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) y.1 v s := by
      intro v s
      simp only [zAt, y, one_mul]
    have h1 : evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h V y := by
      show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ) = (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ)
      simp only [hz]
    have hy : IsTr (fun τ => (atR D M τ : Matrix (Fin n) (Fin n) ℂ)) y f := by
      intro τ
      rw [hf τ]
      show _ = (atR D M τ : Matrix (Fin n) (Fin n) ℂ) * (crdB (embT D) B τ * z.1 τ)
      rw [hcr, ← Matrix.mul_assoc, ← Units.val_mul]
      unfold atR
      rw [map_mul]
    have h2 := evC_natAct (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (atR D M) y f hy V
    rw [h1]
    exact h2.symm
  · unfold actC
    rw [natActR_natActR]
    have he : (fun v s => hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M) v s *
        hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M⁻¹) v s) = fun _ _ => 1 := by
      funext v s
      have hm : ∀ τ, ((1 : GL (Fin n) ℂ) * atR D M τ * (1 : GL (Fin n) ℂ)⁻¹) * ((1 : GL (Fin n) ℂ) * atR D M⁻¹ τ * (1 : GL (Fin n) ℂ)⁻¹) = (1 : GL (Fin n) ℂ) := by
        intro τ
        simp only [one_mul, inv_one, mul_one, atR, ← map_mul, mul_inv_cancel, map_one]
      unfold hAt
      split_ifs
      · rw [← map_mul, hm, map_one]
      · rw [← invT_mul, ← map_mul, hm, map_one, invT_one]
    rw [he, natActR_one]

end GlobalTheory.TwV.DelA

end
