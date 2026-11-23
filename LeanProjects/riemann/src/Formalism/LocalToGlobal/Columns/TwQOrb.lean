import Formalism.LocalToGlobal.Columns.QdfFrameRatio
import Formalism.LocalToGlobal.Columns.CoefColLemmas

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QOrb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_at_rat (q : QLoc hc n Q Θ) (P : Q) (γ : GL (Fin n) E) : q.at P (bc (iA F E) γ) = bc (q.phi P) γ := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rfl

theorem qdf_at_mul (q : QLoc hc n Q Θ) (P : Q) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P (x * y) = q.at P x * q.at P y := by
  show bc _ (bc _ (x * y)) = _
  rw [map_mul, map_mul]

theorem qdf_at_inv (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : q.at P x⁻¹ = (q.at P x)⁻¹ := by
  show bc _ (bc _ x⁻¹) = _
  rw [map_inv, map_inv]

theorem qdf_levUQ_le (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ levU hc n ST SG H := inf_le_left

theorem qdf_levUQ_at (H : Subgroup (GLG E n SG)) (q : QLoc hc n Q Θ) {κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : κ ∈ levUQ hc n ST SG Q H q) (P : Q) : q.at P κ ∈ q.U P :=
  (Subgroup.mem_iInf.1 h.2) P

theorem qdf_ratio_val (p p' : DecoF E n ST SG Q) (γ : Sp E n ≃ₗ[E] Sp E n) (hN : p'.deco.1.N = gmap γ p.deco.1.N) (P : Q) :
    (qdRatio p p' γ hN P).1 = (p'.fr P)⁻¹ * γ * p.fr P := rfl

variable (H : Subgroup (GLG E n SG))

theorem qdf_orbit_of_rel (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p p' : DecoF E n ST SG Q}
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 p') (γ : URat hc n) (κ : levUQ hc n ST SG Q H q)
    (e : (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    ∃ a : UF E n × H × Θ.grp, a.1 = ratHom hc n γ ∧ a.2.1 = levRed hc n ST SG H ⟨_, qdf_levUQ_le H q κ.2⟩ ∧ p' = a • p := by
  have hκ : (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ levU hc n ST SG H := qdf_levUQ_le H q κ.2
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [e]; exact rlc_decoOf_sm hc n ST SG H γ ⟨_, hκ⟩ x
  rw [hx.1, hx'.1] at hd
  have hN : p'.deco.1.N = gmap (ratHom hc n γ).1 p.deco.1.N := by rw [hd]; rfl
  have hinj : ∀ a b : GL (Fin n) E, Formalism.UG.glEquiv a = Formalism.UG.glEquiv b → a = b := fun a b h =>
    Units.ext (Matrix.ext_of_mulVec_single fun j => by
      have := congrArg (fun g : Sp E n ≃ₗ[E] Sp E n => g (Pi.single j 1)) h
      simpa [Formalism.UG.glEquiv] using this)
  have hγ : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) :=
    hinj _ _ (by rw [glEquiv_toGLm]; rfl)
  have hθ : ∀ P : Q, qdRatio p p' (ratHom hc n γ).1 hN P ∈ (Θ P).H := by
    intro P
    rw [← q.U_rat P]
    have h1 := hx.2 P
    have h2 := hx'.2 P
    have h3 := qdf_levUQ_at H q κ.2 P
    have hx'P : q.at P (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        bc (q.phi P) (γ : GL (Fin n) E) * q.at P x * (q.at P κ)⁻¹ := by
      rw [e, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat]
    have key : bc (q.phi P) (qGL n (qdRatio p p' (ratHom hc n γ).1 hN P).1) =
        ((bc (q.phi P) (qGL n (p'.fr P)))⁻¹ * q.at P x') * q.at P κ * ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)⁻¹ := by
      rw [qdf_ratio_val]
      simp only [qGL, map_mul, map_inv]
      rw [hγ, hx'P]
      group
    rw [key]
    exact mul_mem (mul_mem h2 h3) (inv_mem h1)
  refine ⟨(ratHom hc n γ, levRed hc n ST SG H ⟨_, hκ⟩, ⟨fun P => qdRatio p p' (ratHom hc n γ).1 hN P,
    (Subgroup.mem_pi _).2 fun P _ => hθ P⟩), rfl, rfl, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hd
  · funext P
    show p'.fr P = (ratHom hc n γ).1 * p.fr P * ((qdRatio p p' (ratHom hc n γ).1 hN P)⁻¹).1
    rw [Subgroup.coe_inv, qdf_ratio_val]
    group

end QOrb

end Formalism.L2.Col
