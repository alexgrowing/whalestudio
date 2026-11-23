import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusIdentitiesNoKernelOfClauses

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem at_infinity_unitary (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (τ : ι) :
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ =
      gramC J emb τ := by
  have h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ =
      (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ) := by
    ext a b
    simp [atInf, cT, conjTranspose_apply, hc]
  rw [e]
  simp only [gramC, atInf]
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

theorem frame_translate_is_orthonormal (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) (hy : y.IsON) :
    (frameTranslate emb hc γ hγ y).IsON := fun τ => by
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) =
      (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ *
        atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = 1 ∨
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = -1
  rw [e, at_infinity_unitary emb hc γ hγ τ]
  exact hy τ

theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem forms_from_adelic_function (Tf : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (hφ : φ ∈ (D.fm u).Fi i) :
    ∃ g ∈ AdForms (Tf.cls i hi h0).lev (embT D) (lamT u i),
      ∀ c, φ c = fun z => g ((Tf.cls i hi h0).y c) ((Tf.val i hi h0).eY z) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi h0).Fi φ).1 hφ
  refine ⟨g, hg, fun c => ?_⟩
  funext z
  have := congrFun (congrFun hgφ c) ((Tf.val i hi h0).eY z)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
