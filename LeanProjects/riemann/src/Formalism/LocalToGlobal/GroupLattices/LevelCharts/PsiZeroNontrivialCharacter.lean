import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteCompG
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGLev

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

structure CharsG (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ) (Z : Type) [CommGroup Z] where
  psi0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z
  psi_zero_nontrivial_character : ∀ i v h, psi0 i v h ≠ 1
  chi : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}
    {Z : Type} [CommGroup Z]

theorem awayG_le_comap (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    awayG σE J Uloc p ≤ (Uloc v).comap (bc (prV (E := E) v)) :=
  fun x hx => ((mem_awayG σE J Uloc p x).1 hx).2 v hv

def LevAtG.lamG (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg ch.psi0 ch.chi (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtG.typeX (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg ch p hp)⁻¹

def LevAtG.psiX (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.typeX hg ch p hp)⁻¹

theorem LevAtG.psiX_eq (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : X.psiX hg ch p hp = X.lamG hg ch p hp := inv_inv _

variable (σE J Uloc) in

def lamQG (Q : Finset (HeightOneSpectrum (𝓞 F))) (lamQ : ∀ v, v ∈ Q → (Uloc v →* Z)) (p : ℕ)
    (hQ : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) : awayG σE J Uloc p →* Z :=
  prodChar Q Uloc lamQ (awayG σE J Uloc p) (fun v hv => awayG_le_comap p v (hQ v hv))

theorem lamQG_empty (lamQ : ∀ v, v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → (Uloc v →* Z)) (p : ℕ)
    (hQ : ∀ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))), ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    lamQG σE J Uloc ∅ lamQ p hQ = 1 := by
  unfold lamQG prodChar
  simp

end Formalism.L2.G
