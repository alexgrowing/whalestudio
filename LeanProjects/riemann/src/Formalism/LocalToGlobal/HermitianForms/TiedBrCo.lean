import Formalism.LocalToGlobal.HermitianForms.TiedBr
import Formalism.LocalToGlobal.HermitianForms.TiedBrUnit
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Inv

variable {ι : Type} [Fintype ι] {n : ℕ}

open Classical in

def fnInv (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    (Frames G → ℂ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  if h : ∀ τ, IsUnit (M τ).det then
    Classical.choose (LinearMap.exists_leftInverse_of_injective (fnOf G s M)
      (LinearMap.ker_eq_bot.mpr (fnOf_injective G s M h)))
  else 0

theorem fnInv_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : fnInv G s M (fnOf G s M P) = P := by
  classical
  unfold fnInv
  rw [dif_pos h]
  exact LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective (fnOf G s M)
      (LinearMap.ker_eq_bot.mpr (fnOf_injective G s M h)))) P

end Inv

variable {D : D7} {u : D.what₂.Word}

def bZg (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then (iXm D * B') a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

theorem bZg_one (z0 : Fin (D.R.N D.R.m) → D.host.E) : bZg u z0 1 = bZ u z0 := by
  funext a b
  simp only [bZg, bZ, Matrix.mul_one]

def trEv (Tf : FormsTied D u) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] (Fr D D.R.m le_rfl → ℂ) :=
  ((((Tf.cls D.R.m le_rfl).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
    LinearMap.funLeft ℂ ℂ (fun y : Fr D D.R.m le_rfl => (Tf.val D.R.m le_rfl).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))

def coMT (Tf : FormsTied D u) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) :
    ((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ] MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ :=
  fnInv (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
    (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) ∘ₗ trEv Tf c

def coPT (Tf : FormsTied D u) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (w : D.what₂.places.Pl) :
    (D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) :=
  LinearMap.pi fun c => fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u)) (atInf (embT D) (B w c)⁻¹) ∘ₗ
    (LinearMap.proj c ∘ₗ Tf.valP.eW.toLinearMap)

theorem trEv_eq (Tf : FormsTied D u) (φ : Fn D u D.R.m) (c : (D.fm u).clsP) (y : Fr D D.R.m le_rfl) :
    trEv Tf c (φ ((D.fm u).til c)) y = Tf.eWz ((D.mem u).P.evz φ) c ((Tf.val D.R.m le_rfl).eY.symm y) := by
  rw [Tf.evz φ c _ ((Tf.val D.R.m le_rfl).eY.symm
      (y.tr (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (embT D) ((Tf.til.ga c).1)⁻¹)))]
  · rfl
  · intro τ
    simp only [Equiv.apply_symm_apply]
    show y.1 τ = atInf (embT D) (Tf.til.ga c).1.1 τ *
      (atInf (embT D) ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]

end Formalism.L2.Forms
