import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.IdempotentNormalFormsRhoFacts

lemma length_map_quot_le {O X Y : Type*} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (f : X →ₗ[O] Y) (S S' : Submodule O X) :
    Module.length O (↥(S.map f) ⧸ (S'.map f).comap (S.map f).subtype) ≤
      Module.length O (S ⧸ S'.comap S.subtype) := by
  refine Module.length_le_of_surjective
    ((S'.comap S.subtype).mapQ ((S'.map f).comap (S.map f).subtype) (f.submoduleMap S) ?_) ?_
  · intro x hx
    exact Submodule.mem_map_of_mem hx
  · intro y
    obtain ⟨y0, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := LinearMap.submoduleMap_surjective f S y0
    exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem rowRho : StatRowRho := by
  intro O _ _ _ Dw _ M _ _ ρM ε T₁ T₂ _ _ _ _ ρ₁ π γ C₁ CP Hc Cs _ _ cls pr Fs Im X
    hTate hIm hle hX hcup
  refine ⟨(annih pr Im).map Hc.subtype, Submodule.map_mono (annih_anti pr hle),
    (length_map_quot_le Hc.subtype (annih pr Im) (annih pr Fs)).trans
      (annColength O Hc Cs pr Fs Im hle), fun b hb => ?_⟩
  refine ⟨⟨_, hX b hb⟩, ?_, rfl⟩
  refine (mem_annih pr Im _).2 fun x hx => ?_
  obtain ⟨a, ha, hC, rfl⟩ := hIm x hx
  exact hTate a b (hX b hb) ha hC (hcup b hb a ha hC)

section PsiY
variable {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
  {M : Type*} [AddCommGroup M] [Module A M] [Module O M] [IsScalarTower O A M]

def psiY (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) : Ymod r χ E →ₗ[O] M :=
  (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)).restrictScalars O

end PsiY

theorem rowTB : StatRowTB := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ℓ c cB deg Hc F hFH hc hH
    htor hlen
  refine ⟨Hc ⊓ divBy F ((ℓ : O) ^ c), le_inf hFH ?_, ?_, fun φ => ⟨hH φ, ?_⟩⟩
  · intro z hz
    show ((ℓ : O) ^ c) • z ∈ F
    exact F.smul_mem _ hz
  · exact hlen.trans (mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hc))
      (add_le_add le_rfl one_le_two))
  · show ((ℓ : O) ^ c) • (Submodule.mkQ _ (restrictCocycles1 (uRep O (M := M) r χ) Dw
        (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) :
        H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F
    refine htor (psiY r χ E e₁ δ D j Kc k0 φ) ?_ _ (fun g => rfl)
    intro g _ y
    show φ (Submodule.Quotient.mk (uElt r χ g • y, 0)) =
      uElt r χ g • φ (Submodule.Quotient.mk (y, 0))
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Prod.smul_mk, smul_zero]

end Formalism.RepresentationBoundsCohomology.BR
