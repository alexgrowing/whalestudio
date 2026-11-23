import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

namespace Formalism.L2.Forms
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem AdFun_transport (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (g) (hg : g ∈ AdFun S emb) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 = x.1 * κ.1)
    (y y' : Frames (gramC J emb)) (hy : IsTr (atInf emb γ) y' y) :
    g x y = ((S.chi κ)⁻¹ : ℂˣ) * g x' y' := by
  have h2 : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 * (κ⁻¹ : S.U).1 := by
    rw [h]; simp
  have := hg γ hγ x' x κ⁻¹ h2 y y' hy
  rw [this, map_inv]

end Formalism.L2.Forms
