import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGGlob

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem not_mem_of_coprime {p g : ℕ} (h : Nat.Coprime p g) (v : HeightOneSpectrum (𝓞 F))
    (hg : ((g : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have h1 : ((a * p + b * g : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hg)
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

structure LevAtG (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))) (k m t j : ℕ) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = JXU σE J v (splitG i v h) (frG i v h) k m t j

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}

def LevAtG.lamV {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (ψ0 : AddChar (resV F v) Z)
    (χ : ℕ → (resV F v)ˣ →* Z) : Uloc v →* Z :=
  (lamXU σE J v (splitG i v h) (X.frG i v h) k m t j ψ0 χ).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))

def LevAtG.lamGlob {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV i v ((mem_placesOver F (gp i) (hg i) v).1 hv) (ψ0 i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
      (χ i v ((mem_placesOver F (gp i) (hg i) v).1 hv)))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))

theorem LevAtG.lamGlob_apply {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) (x : Up) :
    X.lamGlob hg ψ0 χ Up hUp x = ∏ i : Fin 2, ∏ v ∈ (placesOver F (gp i)).attach,
      X.lamV i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2) (ψ0 i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2))
        (χ i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2))
        ⟨bc (prV (E := E) v.1) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
          hUp i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2) x.2⟩ := by
  unfold LevAtG.lamGlob
  rw [MonoidHom.finset_prod_apply]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold prodChar
  rw [MonoidHom.finset_prod_apply]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rfl

end Formalism.L2.G
