import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Shape

variable {k : Type} [Field k] {n : ℕ}

def blkOf (a t x : ℕ) : ℕ := if x < a then x else a + (x - a) / t

def entN (M : Matrix (Fin n) (Fin n) k) (x y : ℕ) : k := if h : x < n ∧ y < n then M ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

def InJ (a t fc : ℕ) (zl : Bool) (M : Matrix (Fin n) (Fin n) k) : Prop :=
  (∀ x y : Fin n, blkOf a t y < blkOf a t x → M x y = 0) ∧ (∀ x : Fin n, (x : ℕ) < a → M x x = 1) ∧
  (∀ x y : Fin n, (y : ℕ) = fc → M x y = if x = y then 1 else 0) ∧
  (zl = true → ∀ x y : Fin n, (y : ℕ) + 1 = n →
    M x y = (if x = y then 1 else 0) ∧ M y x = (if x = y then 1 else 0))

def blkMat (a t i : ℕ) (M : Matrix (Fin n) (Fin n) k) : Matrix (Fin t) (Fin t) k :=
  fun s s' => entN M (a + i * t + s) (a + i * t + s')

def lamJ (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ) (M : Matrix (Fin n) (Fin n) k) : ℂ :=
  ψ (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then M x y else 0) *
    ∏ i ∈ Finset.range nb, χ i (blkMat a t i M).det

end Shape

section Red

variable (F : Type) [Field F] [NumberField F]

abbrev kv (v : HeightOneSpectrum (𝓞 F)) : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers F)

open Classical in

def redM {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)) :
    Matrix (Fin n) (Fin n) (kv F v) :=
  fun a b => if h : X a b ∈ v.adicCompletionIntegers F then
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨X a b, h⟩ else 0

end Red

section Loc

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure GLoc (σ : E →ₐ[F] E) (gp : Fin 2 → ℕ) where

  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sp_sig : ∀ i v h x, sp i v h (sigR σ (v.adicCompletion F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion F), sp i v h ((1 : E) ⊗ₜ[F] a) = (a, a)

  piG : Fin 2 → 𝓞 E
  piG_norm : ∀ i, (piG i : E) * σ (piG i : E) = (gp i : E)

  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := F) (v.adicCompletion F) (σ (piG i : E)))).1 < 1

  psi0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (kv F v) ℂ
  psi_zero_nontrivial_character : ∀ i v h, psi0 i v h ≠ 1

  chiB : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → MulChar (kv F v) ℂ

variable {F E}
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

def GLoc.phi (G : GLoc F E σ gp) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) :
    E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
  (RingHom.fst _ _).comp (G.sp i v h).toRingHom

def GLoc.mat (G : GLoc F E σ gp) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  ((fr⁻¹ * bc (G.phi i v h) x * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))

structure GLev (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) (a t nb skip fc : ℕ) (zl : Bool) where

  fr : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletion F)
  fr_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin n → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ b, G.phi i v h (y b) = x b) ↔
      ∀ b, (((fr i v h)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  mem : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb, x ∈ S.Uloc v ↔ InJ a t fc zl (redM F v (G.mat i v h (fr i v h) x))

  chi_eq : ∀ x : S.U, (S.chi x : ℂ) = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    (lamJ (G.psi0 i v h) (G.chiB i v h) a t nb skip
      (redM F v (G.mat i v h (fr i v h) (bc (prV (E := E) v) x.1))))⁻¹

  chi_unit : ∀ x : S.U, ‖(S.chi x : ℂ)‖ = 1

end Loc

end Formalism.L2.Forms
