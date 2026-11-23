import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpLApply

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

theorem frames_tr (emb : Tau → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) (z : Frames (gramC J emb)) : ∃ z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z := by
  have h1 : ∀ τ, atInf emb γ τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
    intro τ
    rw [← atInf_mul, ← Units.val_mul, mul_inv_cancel]
    simp [atInf]
  refine ⟨⟨fun τ => atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ, fun τ => ?_⟩, fun τ => ?_⟩
  · rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (h1 τ)).mul (z.2 τ)
  · show z.1 τ = atInf emb γ τ * (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
    rw [← Matrix.mul_assoc, ← atInf_mul, ← Units.val_mul, mul_inv_cancel]
    simp [atInf]

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def EvInj : Prop :=
  ∀ Q : XR G.P ℂ, evC G.P A.rk pos (gramC J emb) (crdB emb A.B) Q = 0 → Q = 0

def PtEx : Prop :=
  ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)), ∃ (c : cls) (γ : GL (Fin n) E) (κ : S.U),
    γ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1)

variable {S emb embLL G A pos embV yc}

theorem valUniq_of (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) : ValUniq S emb embLL G A pos embV yc := by
  intro x i L Q Q' hL h h'
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hp i g
  have hz : evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q - MvPolynomial.map embLL Q') = 0 := by
    funext z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [map_sub, Pi.sub_apply, h.2 g hg c γ hγ κ hpt z z' hz', h'.2 g hg c γ hγ κ hpt z z' hz', sub_self]
    rfl
  have := hi _ hz
  exact MvPolynomial.map_injective embLL embLL.injective (sub_eq_zero.1 this)

end Formalism.L2.G.Cmp

end
