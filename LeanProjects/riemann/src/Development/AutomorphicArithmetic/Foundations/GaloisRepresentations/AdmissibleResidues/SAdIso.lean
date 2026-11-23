import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
open UpperTheory.GalN.V

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

private theorem act_conj (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) k) *ᵥ ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]
  congr 2
  group

private theorem ss_iso (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem irr_iso (h : RepIso r r') (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨hr.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ => rfl
  have hinv := hr.2.2 (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) le_top (fun s v hv => by
    change e _ ∈ W
    have h1 : e v ∈ W := hv
    rw [he] at h1 ⊢
    rw [← act_conj g hg]
    exact hW s _ h1)
  have hW' : W = (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective e.surjective W).symm
  rcases hinv with h0 | h0
  · left
    rw [hW', h0, Submodule.map_bot]
  · right
    rw [hW', h0, Submodule.map_top, LinearEquiv.range]

private theorem tw_iso (χ : Γ →* kˣ) (h : RepIso r r') : RepIso (tw r χ) (tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  simp only [Units.val_mul, tw_val, hg s, Matrix.mul_smul, Matrix.smul_mul]

private theorem comp_iso {Γ' : Type} [Group Γ'] (φ : Γ' →* Γ) (h : RepIso r r') : RepIso (r.comp φ) (r'.comp φ) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun s => hg (φ s)⟩

end Rep

private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    (h : RepIso r r') (H : AttachedSys ι r sat) : AttachedSys ι r' sat :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

end UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso
