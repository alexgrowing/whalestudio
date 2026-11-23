import Formalism.LocalToGlobal.Columns.TwQOrb

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

def FrExists : Prop :=
  ∀ (d : DecoSet E n ST SG) (P : Q), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ y, f y ∈ d.1.at P.1 ↔ y ∈ stdAt E n P.1

theorem qdf_toGLm_ratHom (γ : URat hc n) : toGLm E n (ratHom hc n γ).1 = (γ : GL (Fin n) E) := by
  simp [toGLm, ratHom, Formalism.UG.glEquiv]

variable (H : Subgroup (GLG E n SG))

theorem qdf_rel_of_orbit (q : QLoc hc n Q Θ) {x x' : UAd hc n} {p : DecoF E n ST SG Q} (a : UF E n × H × Θ.grp)
    (hx : FrOver q x.1 p) (hx' : FrOver q x'.1 (a • p)) :
    ∃ (γ : URat hc n) (κ : levUQ hc n ST SG Q H q), ratHom hc n γ = a.1 ∧
      (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
        (κ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
  have hd : decoOf ST SG (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((a.1, a.2.1) : UF E n × H) • decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hx'.1, hx.1]; rfl
  obtain ⟨γ, k, h1, -, e⟩ := rlc_rel_of_orbit hc n ST SG H (a.1, a.2.1) hd
  have hkQ : ∀ P : Q, q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ q.U P := by
    intro P
    have hke : (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * bc (iA F E) (γ : GL (Fin n) E) * (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [e]; group
    have hA := hx'.2 P
    have hB := hx.2 P
    have hθ : (a.2.2.1 P) ∈ (Θ P).H := (Subgroup.mem_pi _).1 a.2.2.2 P (Set.mem_univ _)
    have hC := (q.U_rat P (a.2.2.1 P)).2 hθ
    have hfr : (a • p).fr P = a.1.1 * p.fr P * ((a.2.2.1 P)⁻¹).1 := rfl
    have hγ : toGLm E n a.1.1 = (γ : GL (Fin n) E) := by rw [← h1]; exact qdf_toGLm_ratHom γ
    have key : q.at P (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        ((bc (q.phi P) (qGL n ((a • p).fr P)))⁻¹ * q.at P x')⁻¹ * bc (q.phi P) (qGL n (a.2.2.1 P).1) *
          ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x) := by
      rw [hke, qdf_at_mul, qdf_at_mul, qdf_at_inv, qdf_at_rat, hfr]
      simp only [qGL, map_mul, map_inv, Subgroup.coe_inv]
      rw [hγ]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hA) hC) hB
  exact ⟨γ, ⟨k.1, k.2, Subgroup.mem_iInf.2 hkQ⟩, h1, e⟩

theorem qdf_over_exists (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q) (x : UAd hc n) :
    ∃ p : DecoF E n ST SG Q, FrOver q x.1 p := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ∀ P : Q, Sp E n ≃ₗ[E] Sp E n,
      ∀ (P : Q) y, f P y ∈ (decoOf ST SG x.1).1.at P.1 ↔ y ∈ stdAt E n P.1 :=
    ⟨fun P => (hE (decoOf ST SG x.1) P).choose, fun P => (hE (decoOf ST SG x.1) P).choose_spec⟩
  let p0 : DecoF E n ST SG Q := ⟨(decoOf ST SG x.1, f), fun P y => hf P y⟩
  have hk := fun P : Q => hF x p0 rfl P
  choose g hg using fun P : Q => q.U_dense P _ (hk P).1 (hk P).2
  refine ⟨⟨(decoOf ST SG x.1, fun P => f P * (g P).1), fun P y => ?_⟩, rfl, fun P => ?_⟩
  · show f P ((g P).1 y) ∈ _ ↔ _
    rw [hf P]
    exact (g P).2 y
  · show (Formalism.UG.bc (q.phi P) (qGL n (f P * (g P).1)))⁻¹ * q.at P x.1 ∈ q.U P
    rw [show qGL n (f P * (g P).1) = qGL n (f P) * qGL n (g P).1 from map_mul _ _ _, map_mul, _root_.mul_inv_rev,
      mul_assoc]
    exact hg P

end QCls

end Formalism.L2.Col
